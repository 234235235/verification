package mudspg;

/**
 * An unary operation over an input of type Tr, with result of type T
 * @author dstan
 *
 * @param <T>
 * @param <Tr>
 */
public abstract class UnaryOperation<T,Tr> extends Expression<T> {
	protected Expression<Tr> child;
	protected String op_str = "?";
	
	public UnaryOperation(Expression<Tr> c) {
		child = c;
	}
	
	public UnaryOperation(Expression<Tr> a, String cop_str) {
		child = a;
		op_str = cop_str;
	}
	
	
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + op_str + " " + child + "]";
	}

	/**
	 * The actual method to implement (made concise for the implementer)
	 * @param a
	 * @param b
	 * @return
	 */
	public abstract T apply(Tr c);
	
	public T compute(Evaluation e) {
		// TODO Auto-generated method stub
		return apply(child.compute(e));
	}
	
	// Below all the boring operations ...
	// === comparison over Integer, resulting in Boolean ===
	public static class Not extends UnaryOperation<Boolean,Boolean> {
		public Not(Expression<Boolean> a) {
			super(a, "!");
		}
		@Override
		public Boolean apply(Boolean a) {
			return !a;
		}
	}
}
