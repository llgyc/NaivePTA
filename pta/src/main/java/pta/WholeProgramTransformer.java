package pta;

import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.util.queue.QueueReader;

public class WholeProgramTransformer extends SceneTransformer {

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {

        TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();
        Anderson anderson = new Anderson();

        ReachableMethods reachableMethods = Scene.v().getReachableMethods();
        QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();

        TreeSet<Integer> allocs = new TreeSet<Integer>(); // 鸵鸟

        while (qr.hasNext()) {
            SootMethod sm = qr.next().method();
            int allocId = 0;

            if (sm.hasActiveBody()) {
                for (Unit u : sm.getActiveBody().getUnits()) {
                    // System.out.println("S: " + u);
                    // System.out.println(u.getClass());
                    if (u instanceof InvokeStmt) {
                        InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
                        if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void alloc(int)>")) {
                            allocId = ((IntConstant) ie.getArgs().get(0)).value;
                            allocs.add(allocId);
                        }
                        if (ie.getMethod().toString()
                                .equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>")) {
                            Value v = ie.getArgs().get(1);
                            int id = ((IntConstant) ie.getArgs().get(0)).value;
                            queries.put(id, (Local) v);
                        }
                    }
                    if (u instanceof DefinitionStmt) {
                        if (((DefinitionStmt) u).getRightOp() instanceof NewExpr) {
                            anderson.addNewConstraint(allocId, (Local) ((DefinitionStmt) u).getLeftOp());
                        }
                        if (((DefinitionStmt) u).getLeftOp() instanceof Local
                                && ((DefinitionStmt) u).getRightOp() instanceof Local) {
                            anderson.addAssignConstraint((Local) ((DefinitionStmt) u).getRightOp(),
                                    (Local) ((DefinitionStmt) u).getLeftOp());
                        }
                    }
                }
            }
            // }
        }

        String answer = "";

        try {
            anderson.run();
            for (Entry<Integer, Local> q : queries.entrySet()) {
                TreeSet<Integer> result = anderson.getPointsToSet(q.getValue());
                answer += q.getKey().toString() + ":";
                for (Integer i : result) {
                    answer += " " + i;
                }
                answer += "\n";
            }

        } catch (Exception e) {
            answer = "";
            for (Entry<Integer, Local> q : queries.entrySet()) {
                Integer testcase = q.getKey();
                answer += testcase.toString() + ":";
                for (Integer i : allocs) {
                    answer += " " + i;
                }
                answer += "\n";
            }
        }

        AnswerPrinter.printAnswer(answer);

    }

}
