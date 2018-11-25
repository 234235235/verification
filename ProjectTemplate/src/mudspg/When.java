package mudspg;

import java.util.Iterator;
import java.util.Set;

/**
 * when(bexpr)P runs location P only if bexpr is satisfied
 * @author dstan
 *
 */
public class When extends Location {
	Expression<Boolean> guard;
	Location location;
	
	public When(Expression<Boolean> cguard, Location clocation) {
		super();
		guard = cguard;
		location = clocation;
	}
	
	public Set<Action> getEnabledActions() {
		return location.getEnabledActions();
	}
	
	@Override
	public Iterator<Transition> get_transitions() {
		Iterator<Transition> it = new Iterator<Transition>() {
            private Iterator<Transition> transitions_it = location.get_transitions();
            
            public boolean hasNext() {
                return transitions_it.hasNext();
            }

            public Transition next() {
            	Transition trans = transitions_it.next();
            	Expression<Boolean> new_guard = new BinaryOperation.And(guard, trans.guard);
            	return new Transition(new_guard, trans.action, trans.effect, trans.location);
            }

		};
		return it;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "--[" + guard + "]-->" + location;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
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
		if (!(obj instanceof When)) {
			return false;
		}
		When other = (When) obj;
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
