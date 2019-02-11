import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;



import helper.NBA;
import helper.NotSupportedFormula;
import jhoafparser.storage.StoredEdgeWithLabel;
import jhoafparser.storage.StoredState;
import mudschecker.LTS;
import mudschecker.State;
import mudschecker.Transition;
import mudspg.Action;
import mudspg.BoolVariable;
import mudspg.Expression;
import mudspg.TFormula;
import mudspg.TFormula.Proposition;



public class Part3 extends AbstractChecker {
	
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
//			System.out.println("nope2");
			return null;
		}
		
		
		Collection<State> initStates = model.initialStates;
		if (initStates.isEmpty()) return null;
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
//				System.out.println("Part2, persistenceWit: this should not happen1!");
				return null;
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
						//System.out.println("Part2, persistenceWit: this should not happen2!");
						return null;
					}
					
					oDFS.add(ss); //insert s* in U
					pi.add(0,ss); //Push(pi,s')
					
				}
				else {
					pi.remove(0); //Pop(pi)
					if  (s.satisfies(prop)) {
						if (cycle_Check(s)){//if s not stat a and cycle check (s)
//							System.out.println("nope3");
							//return null;
							//System.out.println("blaabla: ");
							witness.clear();
							
							
							
							Iterator<State> epzit = epzilon.iterator();
							while (epzit.hasNext())
								witness.addFirst(epzit.next());
							
							
							Iterator<State> piit = pi.iterator();
							while (piit.hasNext())
								witness.addFirst(piit.next());
							
					
							
						
							System.out.println(witness);
							//return witness; 
							
						}
						
					}
				}		
			}
		
		}
		
		return null;
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
//					System.out.println("Part2, cycleCheck: this should not happen3!");
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
	

	
	@Override
	public boolean solve(LTS model, TFormula tform, int bound) {
		if (!(tform instanceof TFormula.Proposition)) System.out.println("Keine Proposition") ;
	
		//Iterator<State> it = model.iterator();
		//while (it.hasNext()) {
			//String xy = it.next().toString();
			//String[] wtf = xy.split("\\[");
			//xy = wtf[wtf.length-1];
			//xy = xy.split("\\]")[0];
			//System.out.println(xy);
		//}
		
		LinkedList<State> wit = (LinkedList<State>) persistenceWit(model, (TFormula.Proposition) tform, bound);
		//System.out.println("Wit" + wit);
		if (wit == null) {
			//System.out.println("Wittter");	
			return false;
		} 
		
		return true;
		
	}

}
