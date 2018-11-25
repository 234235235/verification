package mudspg;

/**
 * A program graph transition, made of a new location, an action, and an effect
 * @author dstan
 *
 */
public class Transition {
	public Location location;
	public Action action;
	public Effect effect;
	public Expression<Boolean> guard;
	
	public Transition(Expression<Boolean> guard, Action action, Effect effect, Location location) {
		super();
		this.location = location;
		this.action = action;
		this.effect = effect;
		this.guard = guard;
		assert(action != null);
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "↪trans[" + guard +"]-(" + action + ")-" + effect + "->" + location;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((action == null) ? 0 : action.hashCode());
		result = prime * result + ((effect == null) ? 0 : effect.hashCode());
		result = prime * result + ((guard == null) ? 0 : guard.hashCode());
		result = prime * result
				+ ((location == null) ? 0 : location.hashCode());
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
		if (effect == null) {
			if (other.effect != null) {
				return false;
			}
		} else if (!effect.equals(other.effect)) {
			return false;
		}
		if (guard == null) {
			if (other.guard != null) {
				return false;
			}
		} else if (!guard.equals(other.guard)) {
			return false;
		}
		if (location == null) {
			if (other.location != null) {
				return false;
			}
		} else if (!location.equals(other.location)) {
			return false;
		}
		return true;
	}

}
