/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static pascal.taie.analysis.graph.callgraph.CallGraphs.getCallKind;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO
        // Tips
        if (!callGraph.hasNode(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO
        // if you choose to implement addReachable()
        // via visitor pattern.

        @Override
        public Void visit(New stmt) {
            Obj o = heapModel.getObj(stmt);
            Var v = stmt.getLValue();
            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(o));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var source = stmt.getRValue();
            Var target = stmt.getLValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(source), pointerFlowGraph.getVarPtr(target));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField source = stmt.getFieldRef().resolve();
                Var target = stmt.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(source), pointerFlowGraph.getVarPtr(target));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Var source = stmt.getRValue();
                JField target = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getVarPtr(source), pointerFlowGraph.getStaticField(target));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod target = resolveCallee(null, stmt);
                Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(stmt), stmt, target);
                if (callGraph.addEdge(edge)) {
                    addReachable(target);
                    invokeMethod(stmt, target);
                }
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer p = entry.pointer();
            PointsToSet ps = entry.pointsToSet();

            PointsToSet delta = propagate(p, ps);
            if (p instanceof VarPtr vp) {
                // assert delta != null;
                for (Obj o : delta.getObjects()) {
                    for (LoadField lf : vp.getVar().getLoadFields()) {
                        Var target = lf.getLValue();
                        JField source = lf.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, source);
                        addPFGEdge(instanceField, pointerFlowGraph.getVarPtr(target));
                    }
                    for (StoreField sf : vp.getVar().getStoreFields()) {
                        Var source = sf.getRValue();
                        JField target = sf.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, target);
                        addPFGEdge(pointerFlowGraph.getVarPtr(source), instanceField);
                    }
                    for (LoadArray la : vp.getVar().getLoadArrays()) {
                        Var target = la.getLValue();
                        ArrayIndex source = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(source, pointerFlowGraph.getVarPtr(target));
                    }
                    for (StoreArray sa : vp.getVar().getStoreArrays()) {
                        Var source = sa.getRValue();
                        ArrayIndex target = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(pointerFlowGraph.getVarPtr(source), target);
                    }
                    processCall(vp.getVar(), o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO
        Set<Obj> deltaO = new HashSet<>(pointsToSet.getObjects());
        Set<Obj> orignO = pointer.getPointsToSet().getObjects();
        deltaO.removeAll(orignO);
        PointsToSet delta = new PointsToSet();
        if (!deltaO.isEmpty()) {
            for (Obj o : deltaO) {
                delta.addObject(o);
            }
            for (Obj o : deltaO) {
                pointer.getPointsToSet().addObject(o);
            }
            for (Pointer successor : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(successor, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO
        for (Invoke invoke : var.getInvokes()) {
            JMethod method = resolveCallee(recv, invoke);
            Var mthis = method.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(mthis), new PointsToSet(recv));
            Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(invoke), invoke, method);
            if (callGraph.addEdge(edge)) {
                addReachable(method);
                invokeMethod(invoke, method);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }

    /**
     * When invoke a method, pass the actual params to formal params by adding edges,
     * check if it has a return var and pass it too.
     */
    private void invokeMethod(Invoke invoke, JMethod method) {
        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i ++) {
            Var ap = invoke.getInvokeExp().getArg(i);
            Var fp = method.getIR().getParam(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(ap), pointerFlowGraph.getVarPtr(fp));
        }
        if (invoke.getLValue() != null) {
            for (Var ret : method.getIR().getReturnVars()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(invoke.getLValue()));
            }
        }
    }

}
