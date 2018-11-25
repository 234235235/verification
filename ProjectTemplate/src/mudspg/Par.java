package mudspg;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

/**
 * Auxiliary class, taking care to remember the full body loop during execution
 * @author dstan
 *
 */
public class Par extends Location {
	
	/** Public constructor, taking branches into account
	 * 
	 * @param branches
	 */
	public static Location buildPar(Collection<Location> branches) {
		Location res = null;
		for(Location l: branches) {
			if( res == null) {
				res = l;
				continue;
			}
			res = new Par(res, l);
		}
		return res;
	}
	
	/**
	 * Current body loop (partly "consumed")
	 */
	Location p1;
	
	/**
	 * The next body loop (when p1 is over)
	 */
	Location p2;
	
	Set<Action> sync;
	
	public Par(Location lp1, Location lp2, Set<Action> lsync) {
		p1 = lp1;
		p2 = lp2;
		sync = lsync;
	}
	
	public Par(Location lp1, Location lp2) {
		sync = new HashSet<Action>(lp1.getEnabledActions());
		sync.retainAll(lp2.getEnabledActions());

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
		// Naive: unroll all transitions for p1 and make a Map out of it based on action
		// that is not in sync (otherwise, play it immediately), then iterate on transitions
		// on p2. If an unsync actions occur, play it, otherwise, iterate on each transition
		// in the collection
		
		
		
		Iterator<Transition> it = new Iterator<Transition>() {
			private Transition next = null;
            private Iterator<Transition> it1 = p1.get_transitions();
            private Iterator<Transition> it2 = p2.get_transitions();
            private Iterator<Transition> it_rec = null;
            Transition curP2 = null;
            Map<Action, LinkedList<Transition>> unrolled = new HashMap<Action, LinkedList<Transition>>();
 
            private Location makePar(Location a, Location b) {
    			if( a == Location.terminated && b == Location.terminated)
    				return Location.terminated;
    			return new Par(a, b, sync);
    		}
            
            private void forward() {
            	if( next != null) return;
            	while(it1.hasNext() ) {
            		Transition tr1 = it1.next();
            		if( sync.contains(tr1.action) ) {
            			//add it for later
            			if( !unrolled.containsKey(tr1.action))
            				unrolled.put(tr1.action, new LinkedList<Transition>());
            			unrolled.get(tr1.action).add(tr1);
            		} else {
            			// not in sync alphabet, play it
            			next = new Transition(tr1.guard, tr1.action, tr1.effect, makePar(tr1.location, p2));
            			return;
            		}
            	}
            	//P2
            	while((it_rec != null && it_rec.hasNext()) || it2.hasNext()) {
            		//
            		if( it_rec != null && it_rec.hasNext() ) {
            			Transition tr1 = it_rec.next();
						assert(tr1.action == curP2.action);
            			next = new Transition(new BinaryOperation.And(tr1.guard, curP2.guard),
            						tr1.action,
            						tr1.effect.merge(curP2.effect),
            						new Par(tr1.location, curP2.location, sync));
            			return;
            		}
            		
            		// else, we try to populate again curP2 with a syncing action, and restart it_rec
	            	while(it2.hasNext()) {
	            		Transition tr2 = it2.next();
	            		if( !sync.contains(tr2.action)) {
	            			next = new Transition(tr2.guard, tr2.action, tr2.effect, makePar(p1, tr2.location));
	            			return;
	            		}
	            		else if( unrolled.containsKey(tr2.action)) {
	            			it_rec = unrolled.get(tr2.action).iterator();
	            			curP2 = tr2;
							break;
	            		}
	            		//else{} //well, tr2.action does not appear in p1, so we cannot fire tr2...
	            	}
            	}
            }
            
            public boolean hasNext() {
                forward();
                return next != null;
            }

            public Transition next() {
            	forward();
            	Transition tr = next;
            	next = null;
            	return tr;
            }

        };
		return it;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((p1 == null) ? 0 : p1.hashCode());
		result = prime * result + ((p2 == null) ? 0 : p2.hashCode());
		result = prime * result + ((sync == null) ? 0 : sync.hashCode());
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
		Par other = (Par) obj;
		if (p1 == null) {
			if (other.p1 != null)
				return false;
		} else if (!p1.equals(other.p1))
			return false;
		if (p2 == null) {
			if (other.p2 != null)
				return false;
		} else if (!p2.equals(other.p2))
			return false;
		if (sync == null) {
			if (other.sync != null)
				return false;
		} else if (!sync.equals(other.sync))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "Par [" + p1 + " ||{" + sync + "}" + p2 + "]";
	}
	
	

}
