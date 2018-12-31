import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import com.google.common.collect.Collections2;

import helper.NBA;
import helper.NotSupportedFormula;
import jhoafparser.storage.StoredEdgeWithLabel;
import jhoafparser.storage.StoredState;
import mudschecker.LTS;
import mudschecker.ProgLTS;
import mudschecker.State;
import mudschecker.Transition;
import mudspg.BoolVariable;
import mudspg.Evaluation;
import mudspg.Expression;
import mudspg.Location;
import mudspg.TFormula;
import mudspg.TFormula.Proposition;
import mudspg.UnaryOperation;
import mudspg.Variable;


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
		
		
		//check bounded -> return null if the model has more than n states
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
							return null;
						}
						else {							
							//System.out.println("blaabla: ");
							witness.clear();
							witness.addAll(epzilon);
							//QUESTION: "Ideally, your implementation should not explore the whole state space if a witness 
							// is found at an early stage of the implementation
							//BUT: if we have s.th like T almost always statisfies a, so e.g. we find a witness with a loop
							//where the loop always statisfies a but, there is another path which this is not the case
							//(e.g.) always statisfies b, then if we would return after finding the first witness, we would
							//assume that T almost always statisfies a, but this is not the case? oder nich? im vergewirrt.
							//return witness;
							//System.out.println(witness);
						}
					}
				}
			}
		}
		
		
		return witness;
	}
	
	//QUESTION: return null if a state is explored which is terminal
	//HOW to check wether a state is terminal
	//i cant find any terminal attribute or s.th
	//only possibility -> no outgoing edges implies terminal state
	//then this algorithm doenst need to be changed
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
	
	/* ####################################################### B START ############################################## */

	
	/**
	 * Question b
	 * You are up to hard code the answer for the particular formula of the subject, or compute it for each tform.
	 * For ease of use, the answers to both questions correspond to the number of generated states (even if not reachable/coreachable).
	 */
	public int nbStatesBb(TFormula tform) {
		try {
			NBA nba = new NBA(tform);
		} catch (NotSupportedFormula e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return 0;
	}
	
	public int nbStatesCl(TFormula tform) {
		return 0;
	}
	
	/* ####################################################### B END ################################################ */
	
	/* ####################################################### C START ############################################## */
	
	private class ProductState extends State{
		State ltsState;
		Expression<Boolean> tformState;
				
		public ProductState(State LTS_State, Expression<Boolean> expression) {
			ltsState = LTS_State;
			tformState = expression;
			
		}

		@Override
		public Iterator<Transition> iterator() {
			return null;
		}

		@Override
		public boolean satisfies(Proposition prop) {
			return false;
		
		
		}
		
		@Override
		public String toString() {
			return "("+ltsState+" ;; "+tformState+")";
		}
		
	}
	
	private class ProductLTS extends LTS{
		LTS model;
		TFormula tform;
		NBA nba;
		
		/**
		 * 
		 * @param model LTS model
		 * @param tform TFormula
		 * @throws NotSupportedFormula if Tformula is not valid LTL and translation to NBA fails.
		 */
		public ProductLTS(LTS model,TFormula tform) throws NotSupportedFormula {
			super();
			this.model = model;
			this.tform = tform;
			this.nba = new NBA(tform);
			//Collection<ProductState> init = getInitStates();
			Collection<ProductState> products = productStates();
			createLTS(products);
			printStates(products);

			//initialStates.addAll(getInitStates());
		}

		private void printStates(Collection<ProductState> products) {
			System.out.println("PRODUCT STATES:");
			for (ProductState s : products) {
				System.out.println(s);
			}			
			System.out.println("########");			
		}

		private void createLTS(Collection<ProductState> products) {
			for (ProductState prod : products) {
				Transition tr = new Transition(null, prod);
				//TODO tr.target
			}
			
		}

		private Collection<ProductState> getInitStates() {
			Iterator<State> mod = model.initialStates.iterator();			
			Collection<ProductState> initStates = new ArrayList<ProductState>();
			
			while(mod.hasNext()) {				
				Iterator<List<Integer>> tf = nba.aut.getStoredHeader().getStartStates().iterator();
				while(tf.hasNext()) {
					State modS = mod.next();					
					ArrayList<Integer> xlist = (ArrayList<Integer>) tf.next();
					
					for (int y : xlist) {
						initStates.add(new ProductState(modS,nba.apMap.get(y)));
					}					
				}
				
			}
			
			System.out.println(initStates);
			return initStates;
		}
		
		private Collection<ProductState> productStates() {
			Iterator<State> it = model.iterator();
			Collection<ProductState> prods = new ArrayList<ProductState>();
			
			while (it.hasNext()) {
				State ltsState = it.next();
				Iterator<List<Integer>> tf =  nba.aut.getStoredHeader().getStartStates().iterator();
				while (tf.hasNext()) {
					ArrayList<Integer> n = (ArrayList<Integer>) tf.next();
					
					for (int y : n) {
						prods.add(new ProductState(ltsState,nba.apMap.get(y)));
					}
				}
				
			}
			return prods;
		}
	}

	/**
	 * Question c
	 * @throws NotSupportedFormula 
	 */
	public LTS product(LTS model, TFormula tform, TFormula.Proposition af) throws NotSupportedFormula {
		ProductLTS productLTS = new ProductLTS(model,tform);
		return model; // obviously wrong
	}
	
	/* ####################################################### C END ################################################ */
	
	/**
	 * Question d : wrap it together
	 * Bonus: don't return "false" for non-LTL formula and do the general model checking
	 */
	@Override
	public boolean solve(LTS model, TFormula tform, int bound) {
		
		//Trick of the year return false if the formula is no LTL formula -> just try generate NBA if it fails, 
		//its no LTL formula
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
		
		Expression<Boolean> bexpr = new UnaryOperation.Not(new BoolVariable("a"));
		TFormula.Proposition af = new TFormula.Proposition(bexpr);
		try {
			product(model,tform, af);
		} catch (NotSupportedFormula e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//System.out.println("DAKSFJL: "+model.getClass());
		//State state = model.initialStates.iterator().next();
		//System.out.println("DFDF"+state.getClass());
		
		LinkedList<State> wit = (LinkedList<State>) persistenceWit(model, (Proposition) tform, bound);
		System.out.println(wit);
		if (wit != null) {
			return true;
		}
		
		return false;
		
	}

}
