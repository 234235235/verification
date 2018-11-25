package mudschecker;

import java.util.Iterator;

import mudspg.TFormula;

/**
 * State of a transition system
 * @author dstan
 *
 */
public abstract class State implements Iterable<Transition> {
	/** It is convenient to talk back about the related system
	 * 
	 */
	public LTS system;
	
	/**
	 * Returns an iterator on the set of outgoing transitions
	 * @return
	 */
	public abstract Iterator<Transition> iterator();
	
	/**
	 * Does a proposition hold from this state ?
	 * NB: as opposed to the lecture, the set of atomic propositions is not given a priori.
	 */
	public abstract boolean satisfies(TFormula.Proposition prop);
}
