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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import soot.jimple.toolkits.callgraph.ReachableMethods;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO
        Queue<JMethod> workList = new LinkedList<>();
        workList.offer(entry);

        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (callGraph.addReachableMethod(m)) {
                List<Invoke> callSites = callGraph.callSitesIn(m).toList();
                for (Invoke callSite : callSites) {
                    Set<JMethod> T = resolve(callSite);
                    for (JMethod jm : T) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, jm));
                        workList.offer(jm);
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO
        Set<JMethod> T = new HashSet<>();
        Subsignature s = callSite.getMethodRef().getSubsignature();
        // JClass c = callSite.getMethodRef().getDeclaringClass();
        // What written below is a closer style to the slide.
        // Tips: CallKind k = CallGraphs.getCallKind(callSite);

        if (callSite.isStatic()) {
            T.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(s));
        } else if (callSite.isSpecial()) {
            JClass c = callSite.getMethodRef().getDeclaringClass();
            JMethod m = dispatch(c, s);
            if (m != null) {
                T.add(m);
            }
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            JClass c = callSite.getMethodRef().getDeclaringClass();
            Queue<JClass> workList = new LinkedList<>();
            workList.offer(c);
            while (!workList.isEmpty()) {
                JClass cTmp = workList.poll();
                JMethod m = dispatch(cTmp, s);
                if (m != null) {
                    T.add(m);
                }
                // Maybe a control-flow should be added here.
                workList.addAll(hierarchy.getDirectImplementorsOf(c));
                workList.addAll(hierarchy.getDirectSubinterfacesOf(c));
                workList.addAll(hierarchy.getDirectSubclassesOf(c));
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO
        /*
          If jclass contains non-abstract method that has the same name
          and descriptor as m, return this method; (But how about Interface?)
          else getSubclass of jclass and dispatch it.
          If there is nothing matchable, return null*/
        if (jclass != null) {
            JMethod m = jclass.getDeclaredMethod(subsignature);
            if (m != null && !m.isAbstract()) {
                return m;
            }
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
