/**
 * 
 */
package mudspg;

/**
 * An expression of type T
 * @author dstan
 *
 */
public abstract class Expression<T> extends ASTNode {

	/**
	 * Returns the value after evaluating the expression under a current Evaluation
	 * @param e
	 * @return
	 */
	public abstract T compute(Evaluation e);
	
	
}
