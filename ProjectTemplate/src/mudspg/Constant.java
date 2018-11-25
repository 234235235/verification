package mudspg;


/** Constant value of type T
 * 
 * @author dstan
 *
 * @param <T>
 */
public class Constant<T> extends Expression<T> {
	
	public static Constant<Boolean> true_value = new Constant<Boolean>(true);
	public static Constant<Boolean> false_value = new Constant<Boolean>(false);

	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "C(" + value + ")";
	}
	
	private T value;
	public Constant(T cvalue) {
		value = cvalue;
	}
	@Override
	public T compute(Evaluation e) {
		// TODO Auto-generated method stub
		return value;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		// Eclipse fails to see the following is safe :(
		@SuppressWarnings("unchecked")
		Constant<T> other = (Constant<T>) obj;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}
}
