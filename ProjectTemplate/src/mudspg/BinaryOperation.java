package mudspg;

/**
 * An binary operation over two operands of type Tr, with result of type T
 * @author dstan
 *
 * @param <T>
 * @param <Tr>
 */
public abstract class BinaryOperation<T,Tr> extends Expression<T> {
	protected Expression<Tr> left_side;
	protected Expression<Tr> right_side;
	protected String op_str = "?";
	
	public BinaryOperation(Expression<Tr> a, Expression<Tr> b) {
		left_side = a;
		right_side = b;
	}
	
	public BinaryOperation(Expression<Tr> a, Expression<Tr> b, String cop_str) {
		left_side = a;
		right_side = b;
		op_str = cop_str;
	}
	
	
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + left_side + " " + op_str + " " + right_side + "]";
	}

	/**
	 * The actual method to implement (made concise for the implementer)
	 * @param a
	 * @param b
	 * @return
	 */
	public abstract T apply(Tr a, Tr b);
	
	public T compute(Evaluation e) {
		// TODO Auto-generated method stub
		return apply(left_side.compute(e), right_side.compute(e));
	}
	
	// Below all the boring operations ...
	// === comparison over Integer, resulting in Boolean ===
	public static class Eq extends BinaryOperation<Boolean,Integer> {
		public Eq(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "==");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return a.equals(b);
		}
	}
	
	public static class Neq extends BinaryOperation<Boolean,Integer> {
		public Neq(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "!=");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return !a.equals(b);
		}
	}
	
	public static class Lt extends BinaryOperation<Boolean,Integer> {
		public Lt(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "<");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return a < b;
		}
	}
	
	public static class Gt extends BinaryOperation<Boolean,Integer> {
		public Gt(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, ">");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return a > b;
		}
	}
	
	public static class Geq extends BinaryOperation<Boolean,Integer> {
		public Geq(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, ">=");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return a >= b;
		}
	}
	public static class Leq extends BinaryOperation<Boolean,Integer> {
		public Leq(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "<=");
		}
		@Override
		public Boolean apply(Integer a, Integer b) {
			return a <= b;
		}
	}
	
	// === Boolean operations ===
	public static class And extends BinaryOperation<Boolean,Boolean> {
		public And(Expression<Boolean> a, Expression<Boolean> b) {
			super(a, b, "&&");
		}
		@Override
		public Boolean apply(Boolean a, Boolean b) {
			return a && b;
		}
	}
	public static class Or extends BinaryOperation<Boolean,Boolean> {
		public Or(Expression<Boolean> a, Expression<Boolean> b) {
			super(a, b, "||");
		}
		@Override
		public Boolean apply(Boolean a, Boolean b) {
			return a || b;
		}
	}
	
	// === Integer operations
	public static class Add extends BinaryOperation<Integer,Integer> {
		public Add(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "+");
		}
		@Override
		public Integer apply(Integer a, Integer b) {
			return a + b;
		}
	}
	
	public static class Sub extends BinaryOperation<Integer,Integer> {
		public Sub(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "-");
		}
		@Override
		public Integer apply(Integer a, Integer b) {
			return a - b;
		}
	}
	public static class Mult extends BinaryOperation<Integer,Integer> {
		public Mult(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "*");
		}
		@Override
		public Integer apply(Integer a, Integer b) {
			return a * b;
		}
	}
	
	public static class Div extends BinaryOperation<Integer,Integer> {
		public Div(Expression<Integer> a, Expression<Integer> b) {
			super(a, b, "/");
		}
		@Override
		public Integer apply(Integer a, Integer b) {
			return a / b;
		}
	}
	
}
