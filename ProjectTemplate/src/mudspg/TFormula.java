package mudspg;

/** 
 * A (synctatic) temporal formula representation
 * @author dstan
 *
 */
public class TFormula extends ASTNode {

	public static class Proposition extends TFormula {
		public Expression<Boolean> bexpr;

		public Proposition(Expression<Boolean> bexpr) {
			super();
			this.bexpr = bexpr;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		@Override
		public String toString() {
			return "prop[" + bexpr + "]";
		}
	};
	public static abstract class UnaryOp extends TFormula {
		public TFormula sub;
		String symb;
		public UnaryOp(TFormula sub, String symb) {
			this.sub = sub;
			this.symb = symb;
		}
		/* (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		@Override
		public String toString() {
			return symb.toString() + sub;
		}
	};
	public static class Exist extends UnaryOp {

		public Exist(TFormula sub) {
			super(sub, "E");
		}
	};
	public static class All extends UnaryOp {

		public All(TFormula sub) {
			super(sub, "A");
		}
	};
	public static class Next extends UnaryOp {

		public Next(TFormula sub) {
			super(sub, "X");
		}
	};
	public static class Not extends UnaryOp {
		public Not(TFormula sub) {
			super(sub, "!");
		}
	};
	public static class Globally extends UnaryOp {

		public Globally(TFormula sub) {
			super(sub, "G");
		}
	};
	public static class Eventually extends UnaryOp {

		public Eventually(TFormula sub) {
			super(sub, "F");
		}
	};
	public static abstract class BinaryOp extends TFormula {
		public TFormula suba;
		public TFormula subb;
		String symb;
		public BinaryOp(TFormula suba, TFormula subb, String symb) {
			super();
			this.suba = suba;
			this.subb = subb;
			this.symb = symb;
		}
		/* (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		@Override
		public String toString() {
			return suba + symb + subb;
		}
	};
	public static class Until extends BinaryOp {

		public Until(TFormula suba, TFormula subb) {
			super(suba, subb, "U");
		}	
	}
	public static class WeakUntil extends BinaryOp {
		public WeakUntil(TFormula suba, TFormula subb) {
			super(suba, subb, "W");
		}	
	}
	public static class And extends BinaryOp {
		public And(TFormula suba, TFormula subb) {
			super(suba, subb, "&&");
		}	
	}
	public static class Or extends BinaryOp {
		public Or(TFormula suba, TFormula subb) {
			super(suba, subb, "||");
		}	
	}
}
