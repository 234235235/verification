/**
 * 
 */
package mudspg;

import java.util.Collection;

/**
 * @author dstan
 *
 */
public class Prog extends ASTNode {
	public Location initial;
	public Collection<Action> actions;
	public Collection<Variable<Integer>> ivariables;
	public Collection<Variable<Boolean>> bvariables;
	public Collection<TFormula> properties;
	
	public Prog(Location initial, Collection<Action> actions,
			Collection<Variable<Integer>> ivariables,
			Collection<Variable<Boolean>> bvariables,
			Collection<TFormula> properties
			) {
		super();
		this.initial = initial;
		this.actions = actions;
		this.ivariables = ivariables;
		this.bvariables = bvariables;
		this.properties = properties;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "Prog [initial=" + initial + ", actions=" + actions
				+ ", ivariables=" + ivariables + ", bvariables=" + bvariables
				+ "]";
	}
	
	
	
	
}
