package pta;

import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.javaToJimple.Util;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.queue.QueueReader;

public class WholeProgramTransformer extends SceneTransformer {

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {

        Anderson anderson = new Anderson();
        ReachableMethods reachableMethods = Scene.v().getReachableMethods();
        QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();

        Map<Integer, Type> allocs = new TreeMap<>(); // 保存alloc处的类型和id
        Map<Integer, Type> queries = new TreeMap<>(); // 保存询问的类型

        while (qr.hasNext()) {
            SootMethod sm = qr.next().method();

            int allocId = 0; // 用于传递allocID
            boolean underalloc = false; // 记录是否上面有alloc

            if (sm.hasActiveBody()) {
                for (Unit u : sm.getActiveBody().getUnits()) {

                    if (u instanceof InvokeStmt) {
                        InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
                        if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void alloc(int)>")) {
                            allocId = ((IntConstant) ie.getArgs().get(0)).value;
                            underalloc = true;
                            continue;
                        }
                        if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
                            allocId = ((IntConstant) ie.getArgs().get(0)).value;
                            underalloc = true;
                            continue;
                        }
                        if (ie.getMethod().toString()
                                .equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>")) {
                            Value v = ie.getArgs().get(1);
                            int id = ((IntConstant) ie.getArgs().get(0)).value;
                            queries.put(id, v.getType());
                        }
                        if (ie.getMethod().toString()
                                .equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
                            Value v = ie.getArgs().get(1);
                            int id = ((IntConstant) ie.getArgs().get(0)).value;
                            queries.put(id, v.getType());
                        }
                    }
                    if (u instanceof DefinitionStmt) {
                        if (((DefinitionStmt) u).getRightOp() instanceof NewExpr) {
                            // 可能接在alloc后面也可能不会
                            NewExpr newExp = (NewExpr) (((DefinitionStmt) u).getRightOp());
                            if (underalloc) {
                                allocs.put(allocId, newExp.getType());
                                // or getBaseType?
                            }
                            anderson.addNewConstraint(allocId, (Local) ((DefinitionStmt) u).getLeftOp());
                        }
                        if (((DefinitionStmt) u).getRightOp() instanceof NewArrayExpr) {
                            // todo
                        }
                        if (((DefinitionStmt) u).getLeftOp() instanceof Local
                                && ((DefinitionStmt) u).getRightOp() instanceof Local) {
                            anderson.addAssignConstraint((Local) ((DefinitionStmt) u).getRightOp(),
                                    (Local) ((DefinitionStmt) u).getLeftOp());
                        }
                    }
                    underalloc = false; // 不是
                }
            }
            // }
        }

        String answer = "";

        try {
            anderson.run();
            throw new Exception();
/*            for (Entry<Integer, Local> q : queries.entrySet()) {
                TreeSet<Integer> result = anderson.getPointsToSet(q.getValue());
                answer += q.getKey().toString() + ":";
                for (Integer i : result) {
                    answer += " " + i;
                }
                answer += "\n";
            }*/

        } catch (Exception e) {
            answer = "";
            for (Entry<Integer, Type> q : queries.entrySet()) {
                Integer testcase = q.getKey();
                answer += testcase.toString() + ":";
                for (Entry<Integer, Type> p : allocs.entrySet()) {
                    Type mergedType = (p.getValue()).merge(q.getValue(), Scene.v());
                    if (mergedType == q.getValue()) {
                        answer += " " + p.getKey();
                    }
                }
                answer += "\n";
            }
        }

        AnswerPrinter.printAnswer(answer);

    }

}
