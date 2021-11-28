
package pta;

import soot.Body;
import soot.SootClass;

public class SootMethod {
    Context ctx;
	soot.SootMethod sm;
	SootMethod(Context c, soot.SootMethod m) {
		ctx = c;
		sm = m;
	}
    boolean hasActiveBody() {
        return sm.hasActiveBody();
    }
    Body getActiveBody() {
        return sm.getActiveBody();
    }
    SootClass getDeclaringClass() {
        return sm.getDeclaringClass();
    }
    String getSignature() {
        return sm.getSignature();
    }
    String getName() {
        return sm.getName();
    }
    @Override
	public boolean equals(Object obj) {
		if (obj instanceof SootMethod) {
			SootMethod cm = (SootMethod) obj;
            if (!(getDeclaringClass().getName().equals(
                cm.getDeclaringClass().getName()))) return false;
            if (!(getSignature().equals(cm.getSignature()))) return false;
            if (!ctx.equals(cm.ctx)) return false;
            return true;
		}
		return false;
	}
    @Override
    public int hashCode() {
        final int prime = 998244353;
        int res = 1;
        res = res * prime + ctx.hashCode();
        res = res * prime + getDeclaringClass().getName().hashCode();
        res = res * prime + getSignature().hashCode();
        return res;
    }
}