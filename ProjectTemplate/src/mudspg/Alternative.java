package mudspg;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

/**
 * Alternative alt{::P1 ::P2 …} construct location. When a program is in this location, it can branch
 * non deterministically to any location P1, P2 …
 * The branching occurs without any step (so if some Pi cannot run, for example Pi=when(false)stmt, the program
 * doesn't deadlock in Pi)
 * @author dstan
 *
 */
public class Alternative extends Location {
	
	private Collection<Location> branches;
	
	/**
	 * Take a collection of Location ("branches") as alternatives
	 * @param cbranches
	 */
	public Alternative(Collection<Location> cbranches) {
		branches = cbranches;
	}
	
	public Alternative(Location a, Location b) {
		branches = new LinkedList<Location>();
		branches.add(a);
		branches.add(b);
	}
	
	@Override
	public Iterator<Transition> get_transitions() {
		// TODO Auto-generated method stub
		Iterator<Transition> it = new Iterator<Transition>() {
			private Iterator<Location> branches_it = branches.iterator();
            private Iterator<Transition> transitions_it = Collections.emptyIterator();

            /** 
             * Unroll the iterators until the next item, if any
             */
            private void gotoNext() {
            	// Beware, some branches may have no outgoing transitions, thus we have to loop
            	while(!transitions_it.hasNext() && branches_it.hasNext())
            		transitions_it = branches_it.next().get_transitions();
            }
            
            public boolean hasNext() {
            	gotoNext();
                return transitions_it.hasNext();
            }

            public Transition next() {
            	gotoNext(); // maybe wasn't called, so we do
            	return transitions_it.next();
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
		return it;
	}
	
	public Set<Action> getEnabledActions() {
		Set<Action> res = new HashSet<Action>();
		for( Location p: branches) {
			res.addAll(p.getEnabledActions());
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((branches == null) ? 0 : branches.hashCode());
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
		if (!(obj instanceof Alternative)) {
			return false;
		}
		Alternative other = (Alternative) obj;
		if (branches == null) {
			if (other.branches != null) {
				return false;
			}
		} else if (!branches.equals(other.branches)) {
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "alt{" + branches + "}";
	}
}

