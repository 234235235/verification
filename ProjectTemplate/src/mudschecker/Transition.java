package mudschecker;
import mudspg.*;

/**
 * Transition to a new state (target) under an action action
 * @author dstan
 *
 */
public class Transition {
	public State target;
	public Action action;
	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
		result = prime * result + ((target == null) ? 0 : target.hashCode());
		return result;
	}
	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof Transition)) {
			return false;
		}
		Transition other = (Transition) obj;
		if (action == null) {
			if (other.action != null) {
				return false;
			}
		} else if (!action.equals(other.action)) {
			return false;
		}
		if (target == null) {
			if (other.target != null) {
				return false;
			}
		} else if (!target.equals(other.target)) {
			return false;
		}
		return true;
	}
	
	// All flavors of constructor
	public Transition(State target) {
		super();
		this.target = target;
		this.action = Action.tau;
	}
	
	public Transition(State target, Action action) {
		super();
		this.target = target;
		this.action = action;
	}
	
	public Transition(Action action, State target) {
		super();
		this.target = target;
		this.action = action;
	}
}
