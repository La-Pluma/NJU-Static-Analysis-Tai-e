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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        //Queue<Node> workList = new LinkedList<>(cfg.getSuccsOf(cfg.getEntry()));
        Queue<Node> workList = new LinkedList<>(cfg.getNodes());
        while(!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in_fact = result.getInFact(node);
            for(Node pred : cfg.getPredsOf(node)) {
                Fact pred_out_fact = result.getOutFact(pred);
                analysis.meetInto(pred_out_fact, in_fact);
            }
            Fact out_fact = result.getOutFact(node);
            if(analysis.transferNode(node, in_fact, out_fact)) {
                for(Node succ : cfg.getSuccsOf(node)) {
                    if(!workList.contains(succ)) {
                        workList.add(succ);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>(cfg.getNodes());
        while(!workList.isEmpty()) {
            Node node = workList.poll();
            Fact out_fact = result.getOutFact(node);
            for(Node succ : cfg.getSuccsOf(node)) {
                Fact succ_in_fact = result.getInFact(succ);
                analysis.meetInto(succ_in_fact, out_fact);
            }
            Fact in_fact = result.getInFact(node);
            if(analysis.transferNode(node, in_fact, out_fact)) {
                for(Node pred : cfg.getPredsOf(node)) {
                    if(!workList.contains(pred)) {
                        workList.add(pred);
                    }
                }
            }
        }
    }
}
