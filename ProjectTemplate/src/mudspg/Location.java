package mudspg;

import java.util.*;

/** 
 * 
 * @author dstan
 * A location in a program graph
 */
public abstract class Location extends ASTNode {
	
	public static Location terminated = new TerminatedLocation();
	
	/**
	 * @return an iterator of the (conditionnal) transitions that can be triggered from this location
	 */
	public abstract Iterator<Transition> get_transitions();
	
	/**
	 * Return a set of possibly firable actions by this Location (and successor), to be overriden
	 * @return
	 */
	public Set<Action> getEnabledActions() {
		return Collections.emptySet();
	}
}

class TerminatedLocation extends Location {
	@Override
	public Iterator<Transition> get_transitions() {
		return Collections.emptyIterator();
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "âœlocation“";
	}
	
}