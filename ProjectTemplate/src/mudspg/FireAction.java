package mudspg;

import java.util.Collections;
import java.util.Iterator;
import java.util.Set;


/**
 * Location that fires an action (with possible effect) to the terminated state 
 *  * @author dstan
 *
 */

public class FireAction extends Location {

	protected Transition transition;
	public FireAction(Action caction, Effect ceffect) {
		assert(caction != null);
		transition = new Transition(new Constant<Boolean>(true), caction, ceffect, Location.terminated);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return transition.toString();
	}

	protected FireAction(Transition t) {
		transition = t;
	}
	
	@Override
	public Iterator<Transition> get_transitions() {
		Iterator<Transition> it = new Iterator<Transition>() {
			private boolean fired = false;
            
            public boolean hasNext() {
            	return !fired;
            }

            public Transition next() {
            	assert(!fired);
            	fired = true;
            	return transition;
            }
        };
		return it;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((transition == null) ? 0 : transition.hashCode());
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
		if (!(obj instanceof FireAction)) {
			return false;
		}
		FireAction other = (FireAction) obj;
		if (transition == null) {
			if (other.transition != null) {
				return false;
			}
		} else if (!transition.equals(other.transition)) {
			return false;
		}
		return true;
	}
	
	// Some hardcoded FireAction:
	// The corresponding action throwing locations
	static public Location breakLocation = new FireAction(Action.breakloop, Effect.identity);
	static public Location abortLocation = new AbortLocation();
	static public Location stopLocation = new Location() {

			@Override
			public Iterator<Transition> get_transitions() {
				// TODO Auto-generated method stub
				return Collections.emptyIterator();
			}

			/* (non-Javadoc)
			 * @see java.lang.Object#toString()
			 */
			@Override
			public String toString() {
				return "Stop";
			}
			
		};
	
	public Set<Action> getEnabledActions() {
		Action a = transition.action;
		if( a != Action.breakloop && a != Action.abort && a != Action.tau)
			return Collections.singleton(a);
		return Collections.emptySet();
	}
}

class AbortLocation extends FireAction {
	public AbortLocation() {
		super(null);
	}
	
	public Iterator<Transition> get_transitions() {
		// Very very stupid reason, I cannot reference this from constructor, so …
		if(transition == null) {
			transition = new Transition(new Constant<Boolean>(true), Action.abort, Effect.identity, this);
		}
		return super.get_transitions();
	}
	
	@Override
	public String toString() {
		return "Abort";
	}
	
}
