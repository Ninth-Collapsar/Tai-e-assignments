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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import javax.xml.bind.annotation.XmlElementDecl;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO
        icfg.entryMethods().forEach(method  -> {
            Node node = icfg.getEntryOf(method);
            result.setInFact(node, analysis.newBoundaryFact(node));
            result.setOutFact(node, analysis.newBoundaryFact(node));
        });

        icfg.forEach(node -> {
            if (icfg.entryMethods().noneMatch(method -> node.equals(icfg.getEntryOf(method)))) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        });
    }

    private void doSolve() {
        // TODO
        workList = new LinkedList<>();
        for (Node node : icfg) {
            workList.offer(node);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = result.getInFact(node);
            Fact out = result.getOutFact(node);

            for (ICFGEdge<Node> i : icfg.getInEdgesOf(node)) {
                analysis.meetInto(analysis.transferEdge(i, result.getOutFact(i.getSource())), in);
            }

            if (analysis.transferNode(node, in, out)) {
                for (Node successor : icfg.getSuccsOf(node)) {
                    if (!workList.contains(successor)) {
                        workList.offer(successor);
                    }
                }
            }
        }

    }
}
