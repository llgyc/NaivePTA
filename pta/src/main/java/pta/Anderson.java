package pta;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import java.util.TreeMap;
import java.util.Map.Entry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Comparator;

import javafx.util.Pair;
import soot.Unit;
import soot.Value;
import soot.Local;
import soot.PrimType;
import soot.Scene;
import soot.SootMethod;
import soot.jimple.AnyNewExpr;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.Ref;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

public class Anderson {
	
	LinkedList<Pair<Pointer, HashSet<Location>>> WL;
	HashMap<Pointer, HashSet<Pointer>> PFG;
	HashSet<UnitWithPos> S;
	HashSet<SootMethod> RM;
	// HashSet<CGEdges> CG;
	HashSet<Edge> CG;
	HashMap<Pointer, HashSet<Location>> pt;
	TreeMap<Integer, Pointer> queries;
	CallGraph ncg;

	Anderson() {
		WL = new LinkedList<>();
		PFG = new HashMap<>();
		S = new HashSet<>();
		RM = new HashSet<>();
		CG = new HashSet<>();
		pt = new HashMap<>();
		queries = new TreeMap<>();
		ncg = Scene.v().getCallGraph();
	}
	
	public void solve(SootMethod entry) throws Exception {
		addReachable(entry);
		while (!WL.isEmpty()) {
			Pair<Pointer, HashSet<Location>> pair = WL.remove();
			Pointer n = pair.getKey();
			HashSet<Location> pts = pair.getValue();
			if (!pt.containsKey(n)) { pt.put(n, new HashSet<>()); }
			HashSet<Location> delta = new HashSet<>();
			for (Location l : pts) {
				if (!pt.get(n).contains(l)) delta.add(l);
			}
			propagate(n, pts);
			if (!(n instanceof OPointer)) {
				for (Location o : delta) {
					for (UnitWithPos uwp : S) {
						Unit u = uwp._u;
						if (!(u instanceof JAssignStmt)) continue;
						JAssignStmt jas = (JAssignStmt) u;
						if (jas.getLeftOp() instanceof JInstanceFieldRef) {
							System.out.println(jas.getRightOp());
							if (!Pointer.acceptable(jas.getRightOp())) continue;
							JInstanceFieldRef jifr = (JInstanceFieldRef) jas.getLeftOp();
							Value x = jifr.getBase();
							String f = jifr.getField().getName();
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							Pointer of = OPointer.getOPointer(o, f);
							Pointer y = Pointer.getPointer(uwp._sm, jas.getRightOp());
							addEdge(y, of);
						}
						if (jas.getRightOp() instanceof JInstanceFieldRef) {
							if (!Pointer.acceptable(jas.getLeftOp())) continue;
							JInstanceFieldRef jifr = (JInstanceFieldRef) jas.getRightOp();
							Value x = jifr.getBase();
							String f = jifr.getField().getName();
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							Pointer of = OPointer.getOPointer(o, f);
							Pointer y = Pointer.getPointer(uwp._sm, jas.getLeftOp());
							addEdge(of, y);
						}
						if (jas.getLeftOp() instanceof JArrayRef) {
							if (!Pointer.acceptable(jas.getRightOp())) continue;
							JArrayRef jar = (JArrayRef) jas.getLeftOp();
							Value x = jar.getBase();
							String f = "*";
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							Pointer of = OPointer.getOPointer(o, f);
							Pointer y = Pointer.getPointer(uwp._sm, jas.getRightOp());
							addEdge(y, of);
						}
						if (jas.getRightOp() instanceof JArrayRef) {
							if (!Pointer.acceptable(jas.getLeftOp())) continue;
							JArrayRef jar = (JArrayRef) jas.getRightOp();
							Value x = jar.getBase();
							String f = "*";
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							Pointer of = OPointer.getOPointer(o, f);
							Pointer y = Pointer.getPointer(uwp._sm, jas.getLeftOp());
							addEdge(of, y);
						}
					}
					processCall(n, o);
				}
			}
		}
		String ans = "";
		for (Entry<Integer, Pointer> e : queries.entrySet()) {
			ans += e.getKey().toString() + ":";
			if (pt.containsKey(e.getValue())) {
				ArrayList<Integer> tmp = new ArrayList<>();
				for (Location l : pt.get(e.getValue())) {
					if (l.id > 0) tmp.add(l.id);
				}
				tmp.sort(Comparator.naturalOrder());
				for (Integer i : tmp) {
					ans += " " + i.toString();
				}
			}
			ans += "\n";
		}
		AnswerPrinter.printAnswer(ans);
	}

	void addReachable(SootMethod m) throws Exception {
		if (RM.contains(m)) return;
		RM.add(m);
		if (!m.hasActiveBody()) return;
		int cnt = 0, allocId = 0;
		for (Unit u : m.getActiveBody().getUnits()) {
			++cnt;
			UnitWithPos uwp = new UnitWithPos(m, cnt, u);
			if (!S.contains(uwp)) {	S.add(uwp);	}
			if (u instanceof InvokeStmt) {
				InvokeExpr ie = ((InvokeStmt) u).getInvokeExpr();
				if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void alloc(int)>")) {
					allocId = ((IntConstant) ie.getArgs().get(0)).value;
					continue;
				}
				if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>")) {
					Value v = ie.getArgs().get(1);
					int id = ((IntConstant) ie.getArgs().get(0)).value;
					Pointer p = Pointer.getPointer(m, v);
					queries.put(id, p);
				}
			} else if (u instanceof DefinitionStmt) {
				DefinitionStmt ds = (DefinitionStmt) u;
				if (ds.getRightOp() instanceof AnyNewExpr) {
					Location l;
					if (allocId != 0) {
						l = new Location(true, allocId);
						allocId = 0;
					} else {
						l = new Location(false, 0);
					}
					HashSet<Location> s = new HashSet<>();
					s.add(l);
					// shouldn't happen
					if (ds.getLeftOp() instanceof JInstanceFieldRef) throw new Exception();
					Pointer p = Pointer.getPointer(m, ds.getLeftOp());
					WL.add(new Pair<>(p, s));
				} else if (Pointer.acceptable(ds.getLeftOp()) 
					&& Pointer.acceptable(ds.getRightOp())) {
					// Include JAssignStmt & JIdentityStmt
					System.out.println(ds.getLeftOp());
					Pointer x = Pointer.getPointer(m, ds.getLeftOp());
					Pointer y = Pointer.getPointer(m, ds.getRightOp());
					addEdge(y, x);
				}
			} else if (u instanceof JReturnStmt) {
				Value v = ((JReturnStmt) u).getOp();
				Pointer r = Pointer.getPointer(m, v);
				Pointer mret = RPointer.getRPointer(m, "#ret");
				addEdge(r, mret);
			}
		}
		// static call
		for (Unit u : m.getActiveBody().getUnits()) {
			InvokeExpr ie;
			if (u instanceof InvokeStmt) { 
				// no return value
				ie = ((InvokeStmt) u).getInvokeExpr();
			} else if (u instanceof AssignStmt && 
				((AssignStmt) u).getRightOp() instanceof InvokeExpr) { 
				// with return value
				ie = (InvokeExpr)((AssignStmt) u).getRightOp();
			} else continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void alloc(int)>")) 
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>"))
				continue;
			if (!(ie instanceof StaticInvokeExpr)) continue;
			
			StaticInvokeExpr sie = (StaticInvokeExpr) ie;
			// All possible method
			SootMethod tgt = sie.getMethod();
			addReachable(tgt);
			Integer idxcnt = 0;
			for (Value val : sie.getArgs()) {
				Pointer a = Pointer.getPointer(m, val);
				Pointer p = RPointer.getRPointer(tgt, "#" + idxcnt.toString());
				addEdge(a, p);
				idxcnt++;
			}
			if (u instanceof AssignStmt) {
				Value val = ((AssignStmt) u).getLeftOp();
				Pointer r = Pointer.getPointer(m, val);
				Pointer mret = RPointer.getRPointer(tgt, "#ret");
				addEdge(mret, r);
			}

		}
	}	

	void processCall(Pointer x, Location o) throws Exception {
		HashSet<UnitWithPos> S_clone = (HashSet<UnitWithPos>)(S.clone());
		for (UnitWithPos uwp : S_clone) {
			Unit u = uwp._u;
			InvokeExpr ie;
			if (u instanceof InvokeStmt) { 
				// no return value
				ie = ((InvokeStmt) u).getInvokeExpr();
			} else if (u instanceof AssignStmt && 
				((AssignStmt) u).getRightOp() instanceof InvokeExpr) { 
				// with return value
				ie = (InvokeExpr)((AssignStmt) u).getRightOp();
			} else continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void alloc(int)>")) 
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>"))
				continue;
			if (ie instanceof StaticInvokeExpr) continue;
			InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
			Value v = iie.getBase();
			Pointer xx = Pointer.getPointer(uwp._sm, v);
			if (!xx.equals(x)) continue;
			
			// All possible method
			Iterator<Edge> it = ncg.edgesOutOf(u);
			while (it.hasNext()) {
				Edge e = it.next();
				SootMethod m = e.tgt();
				// add <m_this, o_i> 
				HashSet<Location> s = new HashSet<>();
				s.add(o); 
				Pointer mthis = RPointer.getRPointer(m, "#this");
				WL.add(new Pair<>(mthis, s));
				if (!CG.contains(e)) {
					CG.add(e);
					addReachable(m);
					Integer idxcnt = 0;
					for (Value val : iie.getArgs()) {
						Pointer a = Pointer.getPointer(uwp._sm, val);
						Pointer p = RPointer.getRPointer(m, "#" + idxcnt.toString());
						addEdge(a, p);
						idxcnt++;
					}
					if (u instanceof AssignStmt) {
						Value val = ((AssignStmt) u).getLeftOp();
						Pointer r = Pointer.getPointer(uwp._sm, val);
						Pointer mret = RPointer.getRPointer(m, "#ret");
						addEdge(mret, r);
					}
				}
			}
			// TODO: more detailed dispatch
		}
	}

	void addEdge(Pointer s, Pointer t) {
		// Sanity check
		if (!PFG.containsKey(s)) { PFG.put(s, new HashSet<>()); }
		if (PFG.get(s).contains(t)) return;
		PFG.get(s).add(t);
		// Sanity check
		if (!pt.containsKey(s)) { pt.put(s, new HashSet<>()); }
		if (!pt.get(s).isEmpty()) {
			WL.add(new Pair<>(t, pt.get(s)));
		}
	}

	void propagate(Pointer n, HashSet<Location> pts) {
		if (pts.isEmpty()) return;
		// Sanity check
		if (!pt.containsKey(n)) { pt.put(n, new HashSet<>()); }
		pt.get(n).addAll(pts);
		if (!PFG.containsKey(n)) { PFG.put(n, new HashSet<>()); }
		for (Pointer s : PFG.get(n)) {
			WL.add(new Pair<>(s, pts));
		}
	}
	
}

class SameMethod {
	public static boolean test(SootMethod m1, SootMethod m2) {
		if (!(m1.getDeclaringClass().getName().equals(
			m2.getDeclaringClass().getName()))) return false;
		if (!(m1.getName().equals(m2.getName()))) return false;
		return true;
	}
}

abstract class Pointer {
	public static Set<Pointer> ptrs = new HashSet<>();
	public static Pointer getPointer(SootMethod m, Value v) throws Exception {
		// if (v instanceof IntConstant) {
		// 	int qid = ((IntConstant) v).value;
		// 	return QPointer.getQPointer(m, qid);
		// } else 
		if (v instanceof Local) {
			return LPointer.getLPointer(m, (Local) v);
		} else if (v instanceof Ref) {
			if (v instanceof JInstanceFieldRef) throw new Exception();
			return RPointer.getRPointer(m, (Ref) v);
		} else throw new Exception();
	}
	public static boolean acceptable(Value v) {
		if (v == null) System.out.println("fuck");
		if (v instanceof Local) return true;
		if (v instanceof Ref) {
			if (!(v instanceof JInstanceFieldRef)) return true;
		}
		return false;
	}
	/*
	sm -> Class && Method
	Types:
	- Query (now deleted)
	- Variables
		+ Local
		+ Ref (Static, Params, This)
	- Object Field
	*/
}

// class QPointer extends Pointer {
// 	public static Pointer getQPointer(SootMethod m, int qid) {
// 		QPointer tmp = new QPointer(m, qid);
// 		for (Pointer p : ptrs) {
// 			if (p.equals(tmp)) return p;
// 		}
// 		ptrs.add(tmp);
// 		return tmp;
// 	}
// 	QPointer(SootMethod m, int qid) {
// 		super(m);
// 		queryID = qid;
// 	}
// 	int queryID;
// 	public boolean equals(Object obj) {
// 		if (obj instanceof QPointer) {
// 			QPointer qp = (QPointer) obj;
// 			if (!SameMethod.test(sm, qp.sm)) return false;
// 			if (queryID != qp.queryID) return false;
// 			return true;
// 		}
// 		return false;
// 	}
// }

class LPointer extends Pointer {
	public static Pointer getLPointer(SootMethod m, Local l) {
		LPointer tmp = new LPointer(m, l);
		for (Pointer p : ptrs) {
			if (p.equals(tmp)) return p;
		}
		ptrs.add(tmp);
		return tmp;
	}
	LPointer(SootMethod m, Local l) {
		sm = m;
		local = l;
	}
	public SootMethod sm;
	Local local;
	public boolean equals(Object obj) {
		if (obj instanceof LPointer) {
			LPointer lp = (LPointer) obj;
			if (!SameMethod.test(sm, lp.sm)) return false;
			if (!local.getName().equals(lp.local.getName())) return false;
			return true;
		}
		return false;
	}
}

class RPointer extends Pointer {
	public static Pointer getRPointer(SootMethod m, Ref r) {
		RPointer tmp = new RPointer(m, r);
		for (Pointer p : ptrs) {
			if (p.equals(tmp)) return p;
		}
		ptrs.add(tmp);
		return tmp;
	}
	public static Pointer getRPointer(SootMethod m, String s) {
		RPointer tmp = new RPointer(m, s);
		for (Pointer p : ptrs) {
			if (p.equals(tmp)) return p;
		}
		ptrs.add(tmp);
		return tmp;
	}
	RPointer(SootMethod m, String s) {
		sm = m;
		name = s;
	}
	RPointer(SootMethod m, Ref r) {
		sm = m;
		if (r instanceof ParameterRef) {
			Integer idx = ((ParameterRef) r).getIndex();
			name = "#" + idx.toString();
		} else if (r instanceof ThisRef) {
			name = "#this";
		} else {
			name = r.toString();
		}
	}
	public SootMethod sm;
	String name;
	public boolean equals(Object obj) {
		if (obj instanceof RPointer) {
			RPointer rp = (RPointer) obj;
			if (!SameMethod.test(sm, rp.sm)) return false;
			if (!name.equals(rp.name)) return false;
			return true;
		}
		return false;
	}
}

class OPointer extends Pointer {
	public static Pointer getOPointer(Location l, String f) {
		OPointer tmp = new OPointer(l, f);
		for (Pointer p : ptrs) {
			if (p.equals(tmp)) return p;
		}
		ptrs.add(tmp);
		return tmp;
	}
	OPointer(Location l, String f) {
		loc = l;
		field = f;
	}
	Location loc;
	String field;
	public boolean equals(Object obj) {
		if (obj instanceof OPointer) {
			OPointer op = (OPointer) obj;
			// Method not important for OPointer
			// Omit that judgement
			if (!loc.equals(op.loc)) return false;
			if (!field.equals(op.field)) return false;
			return true;
		}
		return false;
	}
}

// class PPointer extends Pointer {
// 	public static Pointer getPPointer() {
// 		PPointer tmp = new PPointer();
// 		for (Pointer p : ptrs) {
// 			if (p.equals(tmp)) return p;
// 		}
// 		ptrs.add(tmp);
// 		return tmp;
// 	}
// 	PPointer() {}
// 	public boolean equals(Object obj) {
// 		if (obj instanceof PPointer) {
// 			return true;
// 		}
// 		return false;
// 	}
// }

class Location {
	public static int p_cnt = 0;
	public static int n_cnt = 0;
	public int id;
	Location(boolean isMarked, int o_id) {
		if (isMarked) {
			p_cnt = Math.max(p_cnt, o_id);
			id = o_id;
		} else id = --n_cnt;
	}
	public boolean equals(Object obj) {
		if (obj instanceof Location) {
			Location l = (Location) obj;
			if (id == l.id) return true;
		}
		return false;
	}
}

// class CGEdges {
// 	public SootMethod from_sm;
// 	public int from_lineno;
// 	public SootMethod to_sm;
// 	CGEdges(SootMethod fsm, int lineno, SootMethod tsm) {
// 		from_sm = fsm;
// 		from_lineno = lineno;
// 		to_sm = tsm;
// 	}
// 	public boolean equals(Object obj) {
// 		if (obj instanceof CGEdges) {
// 			CGEdges cge = (CGEdges) obj;
// 			if (!SameMethod.test(from_sm, cge.from_sm)) return false;
// 			if (!(from_lineno != cge.from_lineno)) return false;
// 			if (!SameMethod.test(to_sm, cge.to_sm)) return false;
// 			return true;
// 		}
// 		return false;
// 	}
// }

class UnitWithPos {
	public SootMethod _sm;
	public int _lineno;
	public Unit _u;
	UnitWithPos(SootMethod sm, int lineno, Unit u) {
		_sm = sm;
		_lineno = lineno;
		_u = u;
	}
	public boolean equals(Object obj) {
		if (obj instanceof UnitWithPos) {
			UnitWithPos uwp = (UnitWithPos) obj;
			if (!SameMethod.test(_sm, uwp._sm)) return false;
			if (!(_lineno != uwp._lineno)) return false;
			return true;
		}
		return false;
	}
}