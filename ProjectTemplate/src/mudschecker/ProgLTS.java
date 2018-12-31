package mudschecker;

import java.util.Iterator;
import java.util.LinkedList;

import mudspg.*;

/**
 * LTS implementation of a program graph
 * @author dstan
 *
 */
public class ProgLTS extends LTS {
	public ProgLTS(Prog p) {
		super();
		Evaluation ev_init = new Evaluation(p.ivariables, p.bvariables);
		ProgState init = new ProgState(p.initial, ev_init);
		initialStates = new LinkedList<State>();
		initialStates.add(init);
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "Prog[alt{" + initialStates + "}]";
	}
	
}

class ProgState extends State {
	Evaluation ev;
	Location location;
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "State(" + location + "," + ev + ")";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((ev == null) ? 0 : ev.hashCode());
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
		if (!(obj instanceof ProgState)) {
			return false;
		}
		ProgState other = (ProgState) obj;
		if (ev == null) {
			if (other.ev != null) {
				return false;
			}
		} else if (!ev.equals(other.ev)) {
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

	public ProgState(Location location, Evaluation ev) {
		super();
		this.ev = ev;
		this.location = location;
		/*System.out.println("#########");
		System.out.println(ev);
		System.out.println(location);
		System.out.println("#########");*/
	}
	
	
	/**
	 * TODO caching ?
	 */
	public Iterator<mudschecker.Transition> iterator() {
		// Basically just chain the transition with the effect
		Iterator<mudschecker.Transition> it = new Iterator<mudschecker.Transition>() {
			private Iterator<mudspg.Transition> prog_it = location.get_transitions();
            private mudspg.Transition next_tr;
            
            /** Move forward up to the next prog transition
             * 
             */
			private void forward() {
				if(next_tr != null)
					return;
				while(prog_it.hasNext()) {
					next_tr = prog_it.next();
					if(next_tr.guard.compute(ev)) // guard is satisfied, we'll use this trans
						return;
					next_tr = null;
				}
			}
			
            public boolean hasNext() {
                forward();
                return next_tr != null;
            }

            public mudschecker.Transition next() {
            	forward();
            	mudschecker.Transition tr = new mudschecker.Transition(next_tr.action, new ProgState(next_tr.location, next_tr.effect.apply(ev)));
            	next_tr = null;
            	return tr;
            }
        };
		return it;
	}

	@Override
	public boolean satisfies(TFormula.Proposition prop) {
		return prop.bexpr.compute(ev);
	}
}