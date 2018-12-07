package mudspg;

import java.util.*;

/**
 * An effect decribes how to modify program evaluation during a transition.
 * @author dstan
 *
 */
public class Effect extends ASTNode {
	static public Effect identity = new Effect(); //Identity effect, basically, nothing touched
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if(assignements.isEmpty())
			return "∅";
		return "[assignements=" + assignements + "]";
	}

	private List<Assignement> assignements;
	public Effect() {
		assignements = new LinkedList<Assignement>();
	}
	
	public void addBAss(Variable<Boolean> v, Expression<Boolean> e){
		Assignement ass = new Assignement();
		ass.bvar = v; ass.bexpr = e;
		assignements.add(ass);
	}
	
	public void addIAss(Variable<Integer> v, Expression<Integer> e){
		Assignement ass = new Assignement();
		ass.ivar = v; ass.iexpr = e;
		assignements.add(ass);
	}
	
	/**
	 * 
	 * @param ev
	 * @return fresh evaluation after applying the effect
	 */
	public Evaluation apply(Evaluation ev) {
		ev = ev.copy();
		for(Assignement ass: assignements) {
			if(ass.ivar != null) {
				ev.set_int(ass.ivar, ass.iexpr.compute(ev));
			}
			if(ass.bvar != null) {
				ev.set_bool(ass.bvar, ass.bexpr.compute(ev));
			}
		}
		return ev;
	}
	
	/**
	 *  Create the effect this \cup effb, as required for a synchronization
	 *  TODO check for consistency
	*/
	public Effect merge(Effect effb) {
		Effect effc = new Effect();
		for(Assignement ass: assignements) {
			effc.assignements.add(ass);
		}
		for(Assignement ass: effb.assignements) {
			effc.assignements.add(ass);
		}
		return effc;
	}
}

class Assignement {
	public Variable<Boolean> bvar;
	public Expression<Boolean> bexpr;
	
	public Variable<Integer> ivar;
	public Expression<Integer> iexpr;
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if(bvar != null)
			return bvar + ":=" + bexpr;
		else
			return ivar + ":=" + iexpr;
	}
}