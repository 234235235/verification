package mudspg;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * Loop do{::P1 ::P2 …} construct location. When a program is in this location, it can branch
 * infinitely often on alt{::P1 ::P2 …}: whenever the first alt is finished, a new cycle
 * occur. The semantics is given through an auxiliary AuxDo construct AuxDo{P1}{P2}.
 * @author dstan
 *
 */
public class Do extends AuxDo {
	/**
	 * Private constructor taking a body Location and loops over it.
	 * @param body
	 */
	public Do(Location body) {
		super(body, body);
	}
	
	/**
	 * 
	 * @param branches
	 */
	public Do(Collection<Location> branches) {
		this(new Alternative(branches));
	}
	

}

/**
 * Auxiliary class, taking care to remember the full body loop during execution
 * @author dstan
 *
 */
class AuxDo extends Location {
	/**
	 * Current body loop (partly "consumed")
	 */
	Location p1;
	
	/**
	 * The next body loop (when p1 is over)
	 */
	Location p2;
	
	public AuxDo(Location lp1, Location lp2) {
		p1 = lp1;
		p2 = lp2;
	}
	
	public Set<Action> getEnabledActions() {
		return p2.getEnabledActions();
	}

	@Override
	public Iterator<Transition> get_transitions() {
		// run p1, except if Action.breakloop produced (in this case, produce a transition to Location.terminated, with Action.tau)
		// if p1p is Location.terminated, replace by p2
		Iterator<Transition> it = new Iterator<Transition>() {
            private Iterator<Transition> transitions_it = p1.get_transitions();
            
            public boolean hasNext() {
                return transitions_it.hasNext();
            }

            public Transition next() {
            	Transition trans = transitions_it.next();
            	//Body loop triggered a break, terminates the loop gracefully (NB: trans.effect should be identity, but
            	//we never know ...)
            	if(trans.action.equals(Action.breakloop))
            		return new Transition(trans.guard, Action.tau, trans.effect, Location.terminated);
            	//If P1 terminated. Have to loop again, remember the body loop was P2
            	if(trans.location.equals(Location.terminated))
            		return new Transition(trans.guard, trans.action, trans.effect, new AuxDo(p2,p2));
            	//Otherwise, classical step of the body
            	return new Transition(trans.guard, trans.action, trans.effect, new AuxDo(trans.location, p2));
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
		result = prime * result + ((p1 == null) ? 0 : p1.hashCode());
		result = prime * result + ((p2 == null) ? 0 : p2.hashCode());
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
		if (!(obj instanceof AuxDo)) {
			return false;
		}
		AuxDo other = (AuxDo) obj;
		if (p1 == null) {
			if (other.p1 != null) {
				return false;
			}
		} else if (!p1.equals(other.p1)) {
			return false;
		}
		if (p2 == null) {
			if (other.p2 != null) {
				return false;
			}
		} else if (!p2.equals(other.p2)) {
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "AuxDo{" + p1 + "}{" + p2 + "}";
	}
}
