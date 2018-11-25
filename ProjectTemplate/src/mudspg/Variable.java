package mudspg;
/**
 * A variable of type T
 * @author dstan
 *
 */
public abstract class Variable<T> extends Expression<T> {
	protected Expression<T> initial;
	public 	String name = null;
}
