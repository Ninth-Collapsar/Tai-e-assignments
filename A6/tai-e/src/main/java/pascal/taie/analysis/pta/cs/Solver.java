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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts()
                    .forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO
        // implement addReachable()
        // via visitor pattern.

        @Override
        public Void visit(New stmt) {
            Var v = stmt.getLValue();
            Pointer pointer = csManager.getCSVar(context, v);
            Obj o = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, o);
            CSObj cso = csManager.getCSObj(heapContext, o);
            PointsToSet pointsToSet = PointsToSetFactory.make(cso);
            workList.addEntry(pointer, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lv = stmt.getLValue();
            Var rv = stmt.getRValue();
            CSVar source = csManager.getCSVar(context, rv);
            CSVar target = csManager.getCSVar(context, lv);
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // v = o.f;
            if (stmt.isStatic()) {
                StaticField source = csManager.getStaticField(stmt.getFieldRef().resolve());
                CSVar target = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // o.f = c;
            if (stmt.isStatic()) {
                StaticField target = csManager.getStaticField(stmt.getFieldRef().resolve());
                CSVar source = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(Invoke callSite) {
            if (callSite.isStatic()) {
                JMethod callee = resolveCallee(null, callSite);
                CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                Context calleeC = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeC, callee);
                invokeMethod(csCallSite, csCallee);
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet newPTS = entry.pointsToSet();
            PointsToSet delta = propagate(pointer, newPTS);
            if (pointer instanceof CSVar csp) {
                Var v = csp.getVar();
                Context context = csp.getContext();
                for (CSObj csObj : delta) {
                    for (LoadField stmt : v.getLoadFields()) {
                        // v = o.f;
                        CSVar target = csManager.getCSVar(context, stmt.getLValue());
                        JField field = stmt.getFieldAccess().getFieldRef().resolve();
                        InstanceField source = csManager.getInstanceField(csObj, field);
                        addPFGEdge(source, target);
                    }
                    for (StoreField stmt : v.getStoreFields()) {
                        // o.f = c;
                        CSVar source = csManager.getCSVar(context, stmt.getRValue());
                        JField field = stmt.getFieldAccess().getFieldRef().resolve();
                        InstanceField target = csManager.getInstanceField(csObj, field);
                        addPFGEdge(source, target);
                    }
                    for (LoadArray stmt : v.getLoadArrays()) {
                        // v = a[i];
                        CSVar target = csManager.getCSVar(context, stmt.getLValue());
                        ArrayIndex source = csManager.getArrayIndex(csObj);
                        addPFGEdge(source, target);
                    }
                    for (StoreArray stmt : v.getStoreArrays()) {
                        // a[i] = c;
                        CSVar source = csManager.getCSVar(context, stmt.getRValue());
                        ArrayIndex target = csManager.getArrayIndex(csObj);
                        addPFGEdge(source, target);
                    }
                    processCall(csp, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.objects()
                .filter(p -> !pointer.getPointsToSet().contains(p))
                .forEach(delta::addObject);
        if (!delta.isEmpty()) {
            delta.forEach(o -> pointer.getPointsToSet().addObject(o));
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> workList.addEntry(s, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO
        recv.getVar().getInvokes().forEach(callSite -> {
            Context callSiteC = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(callSiteC, callSite);
            JMethod callee = resolveCallee(recvObj, callSite);
            Context calleeC = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeC, callee);
            CSVar pointer = csManager.getCSVar(calleeC, callee.getIR().getThis());
            workList.addEntry(pointer, PointsToSetFactory.make(recvObj));
            invokeMethod(csCallSite, csCallee);
        });
    }

    private void invokeMethod(CSCallSite csCallsite, CSMethod csCallee) {
        // NEW TODO
        Invoke callSite = csCallsite.getCallSite();
        Context callSiteC = csCallsite.getContext();
        Context calleeC = csCallee.getContext();
        if (!callGraph.getCalleesOf(csCallsite).contains(csCallee)) {
            CallKind callKind = null;
            if (callSite.isStatic()) {
                callKind = CallKind.STATIC;
            } else if (callSite.isSpecial()) {
                callKind = CallKind.SPECIAL;
            } else if (callSite.isVirtual()) {
                callKind = CallKind.VIRTUAL;
            } else if (callSite.isInterface()) {
                callKind = CallKind.INTERFACE;
            }
            if (callKind != null) {
                callGraph.addEdge(new Edge<>(callKind, csCallsite, csCallee));
                addReachable(csCallee);
                List<Var> actualParams = callSite.getRValue().getArgs();
                List<Var> formalParams = csCallee.getMethod().getIR().getParams();
                // a, b, c = o.m(i, j, k);
                // from i, j, k to x, y, z
                // def returnType method(Type x, Type y, Type z):
                assert formalParams.size() == actualParams.size();
                for (int i = 0; i < formalParams.size(); i ++) {
                    CSVar source = csManager.getCSVar(callSiteC, actualParams.get(i));
                    CSVar target = csManager.getCSVar(calleeC, formalParams.get(i));
                    addPFGEdge(source, target);
                }
                if (callSite.getLValue() != null) {
                    for (Var res : csCallee.getMethod().getIR().getReturnVars()) {
                        CSVar source = csManager.getCSVar(calleeC, res);
                        CSVar target = csManager.getCSVar(callSiteC, callSite.getLValue());
                        addPFGEdge(source, target);
                    }
                }
            }
        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
