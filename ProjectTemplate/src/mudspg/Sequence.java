package mudspg;


import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;


public class Sequence extends Location {
	Location p1;
	Location p2;
	public Sequence(Location lp1, Location lp2) {
		p1 = lp1;
		p2 = lp2;
	}
	
	public Set<Action> getEnabledActions() {
		Set<Action> res = new HashSet<Action>();
		res.addAll(p1.getEnabledActions());
		res.addAll(p2.getEnabledActions());
		return res;
	}
	
	
	@Override
	public Iterator<Transition> get_transitions() {
		// iterate on p1.get_transitions(), for each of them replace location p1p
		// by Sequence(p1p,p2) only if p1p != Location.terminated, if p1p = Location.terminated, also return p2
		Iterator<Transition> it = new Iterator<Transition>() {
            private Iterator<Transition> transitions_it = p1.get_transitions();
            
            public boolean hasNext() {
                return transitions_it.hasNext();
            }

            public Transition next() {
            	Transition trans = transitions_it.next();
            	if(trans.location.equals(Location.terminated))
            		return new Transition(trans.guard, trans.action, trans.effect, p2);
            	return new Transition(trans.guard, trans.action, trans.effect, new Sequence(trans.location, p2));
            	
            }

        };
		return it;
	}


	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(" + p1 + ";" + p2 + ")";
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
		if (!(obj instanceof Sequence)) {
			return false;
		}
		Sequence other = (Sequence) obj;
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
}
