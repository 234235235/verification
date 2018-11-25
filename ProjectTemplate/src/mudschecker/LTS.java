package mudschecker;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

/**
 * Labelled transition. We can iterate on it to retrieve all states of the system.
 * @author dstan
 *
 */
public abstract class LTS implements Iterable<State> {
	/** Set of initial locations
	 * 
	 */
	public Collection<State> initialStates;
	
	/**
	 * Returns an iterator of the states of the system
	 * @return
	 */
	public Iterator<State> iterator() {
		// We give here a BFS-like exploration of the state space.
		// NB: for infinite state systems, this function may *not* be exhaustive
        final Set<State> visited_ = new HashSet<State>(64);
		final LinkedList<State> open_ = new LinkedList<State>();
		open_.addAll(initialStates);
		visited_.addAll(initialStates);
		
		Iterator<State> it = new Iterator<State>() {
			private Set<State> visited = visited_;
			private LinkedList<State> open = open_;
				
            public boolean hasNext() {
            	return !open.isEmpty();
            }

            public State next() {
            	State res = open.pop();
            	for(Transition tr: res) {
    				if( !visited.contains(tr.target) ) {
    					visited.add(tr.target);
    					open.add(tr.target);
    				}
    			}
            	return res;
            }
        };

		return it;
	}

}
