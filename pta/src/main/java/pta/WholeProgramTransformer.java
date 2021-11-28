package pta;

import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.queue.QueueReader;

public class WholeProgramTransformer extends SceneTransformer {

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {

        try {
            SootClass mainClass = Scene.v().getMainClass();
			Anderson anderson = new Anderson();
			SootMethod m = mainClass.getMethodByName("main");
			anderson.solve(m);
        } catch (Exception e) {
			TreeMap<Integer, Local> queries = new TreeMap<Integer, Local>();

			ReachableMethods reachableMethods = Scene.v().getReachableMethods();
			QueueReader<MethodOrMethodContext> qr = reachableMethods.listener();

			TreeSet<Integer> allocs = new TreeSet<Integer>(); // Be an ostrich!

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
					}
				}
				// }
			}

			String answer = "";

            answer = "";
            for (Entry<Integer, Local> q : queries.entrySet()) {
                Integer testcase = q.getKey();
                answer += testcase.toString() + ":";
                for (Integer i : allocs) {
                    answer += " " + i;
                }
                answer += "\n";
            }
			
			AnswerPrinter.printAnswer(answer);
        }


    }

}
