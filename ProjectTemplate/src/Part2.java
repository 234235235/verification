import java.util.List;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import helper.NBA;
import helper.NotSupportedFormula;
import jhoafparser.storage.StoredEdgeWithLabel;
import jhoafparser.storage.StoredState;
import mudschecker.LTS;
import mudschecker.State;
import mudschecker.Transition;
import mudspg.TFormula;
import mudspg.TFormula.Proposition;


public class Part2 extends AbstractChecker {
	
	//FOR QUESTION A #######################################
	List<State> oDFS = new LinkedList<State>(); //U
	List<State> pi = new LinkedList<State>(); //pi
	List<State> iDFS = new LinkedList<State>(); //V
	List<State> epzilon = new LinkedList<State>(); //epzilon
	//######################################################
	
	
	/* ######################################################## A ############################################### */
	/** 
	 * Question a
	 */
	
	public List<State> persistenceWit(LTS model, TFormula.Proposition prop, int bound) {
		LinkedList<State> witness = new LinkedList<State>();
		
		
		//check bounded
		Part1 p1 = new Part1();
		boolean bounded = p1.checkBounded(model, bound);
		if (!bounded) {
			System.out.println("nope2");
			return null;
		}
		Collection<State> initStates = model.initialStates;
		Iterator<State> it = initStates.iterator();
		while(!oDFS.containsAll(initStates)){ //while S0 not completely contained in U
			State s0 = null;
			while (it.hasNext()) { //Choose s0 el S0 \ U
				s0 = it.next();
				if (!oDFS.contains(s0)) {
					break;
				}
			}
			if (s0 == null) {
				System.out.println("Part2, persistenceWit: this should not happen1!");
			}
			oDFS.add(s0); //insert s0 in U
			pi.add(0,s0); //Push pi, s0
			
			while(!pi.isEmpty()) {
				State s = pi.get(0); //Top(pi)
				LinkedList<State> post = getPost(s); //Post(s)
				if (!oDFS.containsAll(post)) { //if Post(s) not completely contained in U
					Iterator<State> itpost = post.iterator();
					State ss = null;
					while(itpost.hasNext()) { //Choose s' el Post(s) \ U
						ss = itpost.next();
						if (!oDFS.contains(ss)) {
							break;
						}
					}
					
					if (ss == null) {
						System.out.println("Part2, persistenceWit: this should not happen2!");
					}
					
					oDFS.add(ss); //insert s* in U
					pi.add(0,ss); //Push(pi,s')
					
				}
				else {
					pi.remove(0); //Pop(pi)
					if (cycle_Check(s)) {
						if (!s.satisfies(prop)) {//if s not stat a and cycle check (s)
							System.out.println("nope3");
							//return null;
						}
						else {							
							System.out.println("blaabla: ");
							witness.addAll(epzilon);
							System.out.println(witness);
							return witness;
						}
					}
				}
			}
		}
		
		
		return witness;
	}
	
	private boolean cycle_Check(State s) {
		epzilon.clear();
		epzilon.add(0,s); //Push(e,s)
		iDFS.add(s); //insert s in V
		while (!epzilon.isEmpty()) { //while epzilon not empty
			State ss = epzilon.get(0); //s' = Top(e)
			LinkedList<State> post = getPost(ss);
			if (post.contains(s)) { //if s el Post(s')
				epzilon.add(0,s); //Push(e,s)
				return true; //return "true"				
			}
			else if (!iDFS.containsAll(post)){ //if Post(s') not completely in V
				Iterator<State> it = post.iterator();
				State sss = null; 
				while(it.hasNext()) { //choose s'' el Post(s') \ V
					sss = it.next();
					if (!iDFS.contains(sss)) {
						break;
					}
				}
				
				if (sss == null) {
					System.out.println("Part2, cycleCheck: this should not happen3!");
				}
				
				iDFS.add(sss); //insert s'' in V
				epzilon.add(0,sss); //Push(e,s'')
			}
			
			else {
				epzilon.remove(0); //Pop(e)
			}
			
		}
		return false;
	}
	
	/**
	 * 
	 * @param s The source state
	 * @return All successor states
	 */
	private LinkedList<State> getPost(State s) {
		Iterator<Transition> it = s.iterator();
		LinkedList<State> res = new LinkedList<State>();
		while (it.hasNext()) {
			res.add(it.next().target);
		}
		
		return res;
	}
	
	/* ######################################################## A END ############################################### */
	/**
	 * Question b
	 * You are up to hard code the answer for the particular formula of the subject, or compute it for each tform.
	 * For ease of use, the answers to both questions correspond to the number of generated states (even if not reachable/coreachable).
	 */
	public int nbStatesBb(TFormula tform) {
		return 0;
	}
	
	public int nbStatesCl(TFormula tform) {
		return 0;
	}
	
	/**
	 * Question c
	 */
	public LTS product(LTS model, TFormula tform, TFormula.Proposition af) {
		return model; // obviously wrong
	}
	
	/**
	 * Question d : wrap it together
	 * Bonus: don't return "false" for non-LTL formula and do the general model checking
	 */
	@Override
	public boolean solve(LTS model, TFormula tform, int bound) {
		try {
			// Demonstration of the helper tools here, you are not forced to use them:
			NBA aphi = new NBA(tform);
			System.out.println("automaton starts in" + aphi.aut.getStoredHeader().getStartStates());
			for( StoredState state: aphi.aut.getStoredStates()) {
				System.out.println("Description of state " + state.getStateId());
				System.out.println("  Is accepting:" + !state.getAccSignature().isEmpty()); // There only one acceptance set, so the
					//acceptance signature is always [] or [0] (the latter if accepting)
				for( StoredEdgeWithLabel edge: aphi.aut.getEdgesWithLabel(state.getStateId())) {
					System.out.println("  transition to " + edge.getConjSuccessors().get(0) + " under condition " + aphi.propOfLabel(edge.getLabelExpr()));	
				}
			}
			System.out.println("Or you may want the HOA format:");
			aphi.printHOA();
		} catch (NotSupportedFormula e) {
			System.out.println("nope1");
			return false; // Not LTL
		}
		
		
		LinkedList<State> wit = (LinkedList<State>) persistenceWit(model, (Proposition) tform, bound);
		System.out.println(wit);
		if (wit != null) {
			return true;
		}
		
		return false;
		
	}

}
