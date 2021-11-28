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
import soot.Scene;
import soot.SootClass;
// import soot.SootMethod;
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
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.FastHierarchy;

public class Anderson {
	
	LinkedList<Pair<Pointer, HashSet<Location>>> WL;
	HashMap<Pointer, HashSet<Pointer>> PFG;
	HashSet<UnitWithPos> S;
	HashSet<SootMethod> RM;
	// HashSet<CGEdges> CG;
	HashSet<CGEdge> CG;
	HashMap<Pointer, HashSet<Location>> pt;
	TreeMap<Integer, HashSet<Pointer>> queries;
	CallGraph ncg;
	HashMap<soot.SootMethod, Integer> sm2id;
	FastHierarchy fh;
	HashMap<Integer, SootClass> id2class;

	Anderson() {
		WL = new LinkedList<>();
		PFG = new HashMap<>();
		S = new HashSet<>();
		RM = new HashSet<>();
		CG = new HashSet<>();
		pt = new HashMap<>();
		queries = new TreeMap<>();
		ncg = Scene.v().getCallGraph();
		sm2id = new HashMap<>();
		fh = Scene.v().getFastHierarchy();
		id2class = new HashMap<>();
	}
	
	public void solve(SootMethod entry) throws Exception {
		addReachable(entry);
		while (!WL.isEmpty()) {
			Pair<Pointer, HashSet<Location>> pair = WL.remove();
			Pointer n = pair.getKey();
			HashSet<Location> pts = pair.getValue();
			System.out.println(n);
			for (Location l : pts) {
				System.out.print(" ");
				
				System.out.print(l.id);
				
			}
			System.out.println();

			if (!pt.containsKey(n)) { pt.put(n, new HashSet<>()); }
			HashSet<Location> delta = new HashSet<>();
			for (Location l : pts) {
				if (!pt.get(n).contains(l)) delta.add(l);
			}
			propagate(n, delta);
			if (!(n instanceof OPointer)) {
				for (Location o : delta) {
					for (UnitWithPos uwp : S) {
						Unit u = uwp._u;
						if (!(u instanceof JAssignStmt)) continue;
						JAssignStmt jas = (JAssignStmt) u;
						if (jas.getLeftOp() instanceof JInstanceFieldRef) {
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
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							String f;
							if (jar.getIndex() instanceof IntConstant) {
								Integer i = ((IntConstant) jar.getIndex()).value;
								f = i.toString();
								// add array.i -> array.*
								Pointer p1 = OPointer.getOPointer(o, f);
								Pointer p2 = OPointer.getOPointer(o, "*");
								addEdge(p1, p2);
								// add array.+ -> array.i
								Pointer p3 = OPointer.getOPointer(o, "+");
								addEdge(p3, p1);
								// add y -> array.i
								Pointer of = OPointer.getOPointer(o, f);
								Pointer y = Pointer.getPointer(uwp._sm, jas.getRightOp());
								addEdge(y, of);
							} else {
								f = "+";
								Pointer of = OPointer.getOPointer(o, f);
								Pointer y = Pointer.getPointer(uwp._sm, jas.getRightOp());
								addEdge(y, of);
								Pointer p1 = OPointer.getOPointer(o, "*");
								addEdge(of, p1);								
							}
						}
						if (jas.getRightOp() instanceof JArrayRef) {
							if (!Pointer.acceptable(jas.getLeftOp())) continue;
							JArrayRef jar = (JArrayRef) jas.getRightOp();
							Value x = jar.getBase();
							Pointer px = Pointer.getPointer(uwp._sm, x);
							if (!px.equals(n)) continue;
							String f;
							if (jar.getIndex() instanceof IntConstant) {
								Integer i = ((IntConstant) jar.getIndex()).value;
								f = i.toString();
								// add array.i -> array.*
								Pointer p1 = OPointer.getOPointer(o, f);
								Pointer p2 = OPointer.getOPointer(o, "*");
								addEdge(p1, p2);
								// add array.+ -> array.i
								Pointer p3 = OPointer.getOPointer(o, "+");
								addEdge(p3, p1);
							} else f = "*";
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
		for (Entry<Integer, HashSet<Pointer>> e : queries.entrySet()) {
			ans += e.getKey().toString() + ":";
			for (Pointer p : e.getValue()) {
				if (pt.containsKey(p)) {
					ArrayList<Integer> tmp = new ArrayList<>();
					for (Location l : pt.get(p)) {
						if (l.id > 0) tmp.add(l.id);
					}
					tmp.sort(Comparator.naturalOrder());
					for (Integer i : tmp) {
						ans += " " + i.toString();
					}
				}
			}
			ans += "\n";
		}
		AnswerPrinter.printAnswer(ans);
	}

	void addReachable(SootMethod m) throws Exception {
		if (RM.contains(m)) return;
		RM.add(m);
		System.out.println("================");
		System.out.println(m.getDeclaringClass().getName()+" "+m.getSignature());
		System.out.println(m.ctx.strlist.size());
		if (m.ctx.strlist.size() > 0) System.out.println(m.ctx.strlist.get(0));
		if (m.ctx.strlist.size() > 1) System.out.println(m.ctx.strlist.get(1));
		if (!m.hasActiveBody()) return;
		Integer cnt = 0;
		Integer allocId = 0;
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
				if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) {
					allocId = ((IntConstant) ie.getArgs().get(0)).value;
					continue;
				}
				if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>")) {
					Value v = ie.getArgs().get(1);
					int id = ((IntConstant) ie.getArgs().get(0)).value;
					Pointer p = Pointer.getPointer(m, v);
					if (!queries.containsKey(id)) { queries.put(id, new HashSet<>()); }
					queries.get(id).add(p);
				}
				if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>")) {
					Value v = ie.getArgs().get(1);
					int id = ((IntConstant) ie.getArgs().get(0)).value;
					Pointer p = Pointer.getPointer(m, v);
					if (!queries.containsKey(id)) { queries.put(id, new HashSet<>()); }
					queries.get(id).add(p);
				}
			} else if (u instanceof DefinitionStmt) {
				DefinitionStmt ds = (DefinitionStmt) u;
				if (ds.getRightOp() instanceof AnyNewExpr) {
					Location l;
					SootClass sc;
					if (ds.getRightOp() instanceof JNewExpr) {
						sc = ((JNewExpr) ds.getRightOp()).getBaseType().getSootClass();
					} else {
						sc = null;
					}
					if (allocId != 0) {
						l = new Location(allocId, m.ctx);
						if (sc != null) {
							if (!id2class.containsKey(allocId)) {
								id2class.put(allocId, sc);
							}
						}
						allocId = 0;
					} else {
						if (!sm2id.containsKey(m.sm)) {
							sm2id.put(m.sm, --Location.n_cnt);
						}
						int tmpId = sm2id.get(m.sm);
						l = new Location(tmpId, m.ctx);
						if (sc != null) {
							if (!id2class.containsKey(tmpId)) {
								id2class.put(tmpId, sc);
							}
						}
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
		cnt = 0;
		for (Unit u : m.getActiveBody().getUnits()) {
			++cnt;
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
			if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) 
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>"))
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>"))
				continue;
			if (!(ie instanceof StaticInvokeExpr)) continue;
			
			StaticInvokeExpr sie = (StaticInvokeExpr) ie;
			// All possible method
			soot.SootMethod ssm = sie.getMethod();
			Context c = new Context(m.ctx.strlist);
			c.add(m.getDeclaringClass().getName()+m.getSignature()+cnt);
			SootMethod tgt = new SootMethod(c, ssm);
			addReachable(tgt);
			Integer idxcnt = 0;
			for (Value val : sie.getArgs()) {
				if (Pointer.acceptable(val)) {
					Pointer a = Pointer.getPointer(m, val);
					Pointer p = RPointer.getRPointer(tgt, "#" + idxcnt.toString());
					addEdge(a, p);
				}
				idxcnt++;
			}
			if (u instanceof AssignStmt) {
				Value val = ((AssignStmt) u).getLeftOp();
				if (Pointer.acceptable(val)) {
					Pointer r = Pointer.getPointer(m, val);
					Pointer mret = RPointer.getRPointer(tgt, "#ret");
					addEdge(mret, r);
				}
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
			if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void alloc(int)>")) 
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.BenchmarkN: void test(int,java.lang.Object)>"))
				continue;
			if (ie.getMethod().toString().equals("<benchmark.internal.Benchmark: void test(int,java.lang.Object)>"))
				continue;
			if (ie instanceof StaticInvokeExpr) continue;
			InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
			Value v = iie.getBase();
			Pointer xx = Pointer.getPointer(uwp._sm, v);
			if (!xx.equals(x)) continue;
			
			// All possible method
			if (id2class.containsKey(o.id)) {
				soot.SootMethod ssm = fh.resolveConcreteDispatch(id2class.get(o.id), iie.getMethod());
				Context c = new Context(uwp._sm.ctx.strlist);
				c.add(uwp._sm.getDeclaringClass().getName()+uwp._sm.getSignature()+uwp._lineno);
				SootMethod m = new SootMethod(c, ssm);
				// add <m_this, o_i> 
				HashSet<Location> s = new HashSet<>();
				s.add(o); 
				Pointer mthis = RPointer.getRPointer(m, "#this");
				WL.add(new Pair<>(mthis, s));
				CGEdge myedge = new CGEdge(uwp._sm, uwp._lineno, m);
				if (!CG.contains(myedge)) {
					CG.add(myedge);
					addReachable(m);
					Integer idxcnt = 0;
					for (Value val : iie.getArgs()) {
						if (Pointer.acceptable(val)) {
							Pointer a = Pointer.getPointer(uwp._sm, val);
							Pointer p = RPointer.getRPointer(m, "#" + idxcnt.toString());
							addEdge(a, p);
						}
						idxcnt++;
					}
					if (u instanceof AssignStmt) {
						Value val = ((AssignStmt) u).getLeftOp();
						if (Pointer.acceptable(val)) {
							Pointer r = Pointer.getPointer(uwp._sm, val);
							Pointer mret = RPointer.getRPointer(m, "#ret");
							addEdge(mret, r);
						}
					}
				}
			} else {
				Iterator<Edge> it = ncg.edgesOutOf(u);
				while (it.hasNext()) {
					Edge e = it.next();
					soot.SootMethod ssm = e.tgt();
					Context c = new Context(uwp._sm.ctx.strlist);
					c.add(uwp._sm.getDeclaringClass().getName()+uwp._sm.getSignature()+uwp._lineno);
					SootMethod m = new SootMethod(c, ssm);
					// add <m_this, o_i> 
					HashSet<Location> s = new HashSet<>();
					s.add(o); 
					Pointer mthis = RPointer.getRPointer(m, "#this");
					WL.add(new Pair<>(mthis, s));
					CGEdge myedge = new CGEdge(uwp._sm, uwp._lineno, m);
					if (!CG.contains(myedge)) {
						CG.add(myedge);
						addReachable(m);
						Integer idxcnt = 0;
						for (Value val : iie.getArgs()) {
							if (Pointer.acceptable(val)) {
								Pointer a = Pointer.getPointer(uwp._sm, val);
								Pointer p = RPointer.getRPointer(m, "#" + idxcnt.toString());
								addEdge(a, p);
							}
							idxcnt++;
						}
						if (u instanceof AssignStmt) {
							Value val = ((AssignStmt) u).getLeftOp();
							if (Pointer.acceptable(val)) {
								Pointer r = Pointer.getPointer(uwp._sm, val);
								Pointer mret = RPointer.getRPointer(m, "#ret");
								addEdge(mret, r);
							}
						}
					}
				}
			}
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
		return m1.equals(m2);
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
		if (v instanceof Local) return true;
		if (v instanceof Ref) {
			if (!(v instanceof JInstanceFieldRef)) return true;
		}
		return false;
	}
	/*
	sm -> Class && Method
	Types:
	- Variables
		+ Local
		+ Ref (Static, Params, This)
	- Object Field
	*/
}

class LPointer extends Pointer {
	public static Pointer getLPointer( SootMethod m, Local l) {
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
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof LPointer) {
			LPointer lp = (LPointer) obj;
			if (!SameMethod.test(sm, lp.sm)) return false;
			if (!local.getName().equals(lp.local.getName())) return false;
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + sm.hashCode();
        res = res * prime + local.getName().hashCode();
        return res;
    }
	@Override
	public String toString() {
		return sm.getDeclaringClass().getName()+sm.getName()+local.getName();
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
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof RPointer) {
			RPointer rp = (RPointer) obj;
			if (!SameMethod.test(sm, rp.sm)) return false;
			if (!name.equals(rp.name)) return false;
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + sm.hashCode();
		res = res * prime + name.hashCode();
        return res;
    }
	@Override
	public String toString() {
		return sm.getDeclaringClass().getName()+sm.getName()+name;
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
	@Override
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
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + loc.hashCode();
		res = res * prime + field.hashCode();
        return res;
    }
	@Override
	public String toString() {
		return loc.toString() + field;
	}
}

class Location {
	public static int n_cnt = 0;
	Context ctx;
	public int id;
	Location(int o_id, Context c) {
		id = o_id;
		ctx = c;
	}
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Location) {
			Location l = (Location) obj;
			if (id != l.id) return false;
			if (!ctx.equals(l.ctx)) return false;
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + ctx.hashCode();
        res = res * prime + id;
        return res;
    }
	@Override
	public String toString() {
		Integer i = id;
		return i.toString();
	}
}

class UnitWithPos {
	public SootMethod _sm;
	public int _lineno;
	public Unit _u;
	UnitWithPos(SootMethod sm, int lineno, Unit u) {
		_sm = sm;
		_lineno = lineno;
		_u = u;
	}
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof UnitWithPos) {
			UnitWithPos uwp = (UnitWithPos) obj;
			if (!SameMethod.test(_sm, uwp._sm)) return false;
			if ((_lineno != uwp._lineno)) return false;
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + _sm.hashCode();
		res = res * prime + _lineno;
        return res;
    }
}

class Context {
	LinkedList<String> strlist;
	Context() { strlist = new LinkedList<>(); }
	Context(LinkedList<String> sml) { strlist = (LinkedList<String>)sml.clone(); }
	public void add(String s) {
		strlist.addFirst(s);
		while (strlist.size() > 2) {
			strlist.removeLast();
		}
	}
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Context) {
			Context ctx = (Context) obj;
			if (strlist.size() != ctx.strlist.size()) return false;
			for (int i = 0; i < strlist.size(); ++i) {
				String str1 = strlist.get(i);
				String str2 = ctx.strlist.get(i);
				if (!str1.equals(str2)) return false;
			}
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + strlist.size();
		for (String s : strlist) {
			res = res * prime + s.hashCode();
		}
        return res;
    }
};

class CGEdge {
	SootMethod from;
	int lineno;
	SootMethod to;
	CGEdge(SootMethod fsm, int line, SootMethod tsm) {
		from = fsm;
		lineno = line;
		to = tsm;
	}
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CGEdge) {
			CGEdge cge = (CGEdge) obj;
			if (!from.equals(cge.from)) return false;
			if (lineno != cge.lineno) return false;
			if (!to.equals(cge.to)) return false;
			return true;
		}
		return false;
	}
	@Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + from.hashCode();
		res = res * prime + lineno;
		res = res * prime + to.hashCode();
        return res;
    }
}