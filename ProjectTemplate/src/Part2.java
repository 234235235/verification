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
							witness.addAll(epzilon);
//							System.out.println(witness);
							return witness;
							
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
	
			return getSize(nba);
		} catch (NotSupportedFormula e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return -1;
	}
	
	public int nbStatesCl(TFormula tform) {
		//String phi = "(aUz) & (bUz)";
		String cl = "a,b,z,(aUz),(bUz),(aUz) & (bUz),-a,-b,-z,-(aUz),-(bUz),-((aUz) & (bUz))";
		String[] cl_arr = cl.split(",");		
		List<String> cl_list = Arrays.asList(cl_arr);
		
		List<String>  subf = cl_list.subList(0, 6);
		List<String> nsubf = cl_list.subList(6, 12);
		
		LinkedHashSet<LinkedHashSet<String>> pM = powerset(cl_arr);
		
		/*
		System.out.println("subf(phi): "+subf);
		System.out.println("-subf(phi) :"+nsubf);
		System.out.println("cl(phi): "+cl_list); */
		
		LinkedList<LinkedHashSet<String>> pS = new LinkedList<LinkedHashSet<String>>();
		Iterator<LinkedHashSet<String>> it = pM.iterator();
		while(it.hasNext()) {
			LinkedHashSet<String> nxt = it.next();
			if (nxt.size() == 6) {
				boolean check = true;
				int c = 0;
				while (c<6) {
					if (nxt.contains(subf.get(c))) {
						if(nxt.contains(nsubf.get(c))) {
							check = false;
						}
					}
					c++;
				}
				if (check) {
					if (nxt.contains("z")) {
						if (!nxt.contains("(aUz)") || !nxt.contains("(bUz)")) {
							continue;
						}
					}
					
					if(nxt.contains("(aUz)")){
						if (!nxt.contains("z")) {
							if (!nxt.contains("a")) {
								continue;
							}
						}
					}
					
					if(nxt.contains("(bUz)")){
						if (!nxt.contains("z")) {
							if (!nxt.contains("b")) {
								continue;
							}
						}
					}
					
					if(nxt.contains("(aUz) & (bUz)")) {
						if (!nxt.contains("(aUz)") || !nxt.contains("(bUz)")){
							continue;
						}
					}
					
					if (nxt.contains("-((aUz) & (bUz))")){
						if (nxt.contains("aUz") || nxt.contains("bUz")) {
							continue;
						}
					}
					
					if (nxt.contains("-(aUz)")){
						if (nxt.contains("a") || nxt.contains("z")) {
							continue;
						}
					}
					
					if (nxt.contains("-(bUz)")){
						if(nxt.contains("b") || nxt.contains("z")) {
							continue;
						}
					}
					
				
					
					
					pS.add(nxt);
				}
			}
	
		}
		
	
		/*Iterator<LinkedHashSet<String>> it1 = pS.iterator();
		System.out.println("");
		System.out.println("################################################");
		System.out.println("PowerSet(maximal) of size "+pS.size()+":" );
		while (it1.hasNext()) {
			LinkedHashSet<String> nxt = it1.next();
			System.out.println(nxt);
		}
		System.out.println("################################################");
		System.out.println("");*/
		
		return pS.size();
	}
	
	private LinkedHashSet<LinkedHashSet<String>> powerset(String[] set) {
	      
        //create the empty power set
        LinkedHashSet<LinkedHashSet<String>> power = new LinkedHashSet<LinkedHashSet<String>>();
      
        //get the number of elements in the set
        int elements = set.length;
      
        //the number of members of a power set is 2^n
        int powerElements = (int) Math.pow(2,elements);
      
        //run a binary counter for the number of power elements
        for (int i = 0; i < powerElements; i++) {
          
            //convert the binary number to a string containing n digits
            String binary = intToBinary(i, elements);
          
            //create a new set
            LinkedHashSet<String> innerSet = new LinkedHashSet<String>();
          
            //convert each digit in the current binary number to the corresponding element
             //in the given set
            for (int j = 0; j < binary.length(); j++) {
                if (binary.charAt(j) == '1')
                    innerSet.add(set[j]);
            }
          
            //add the new set to the power set
            power.add(innerSet);
          
        }
      
        return power;
    }
  
    private String intToBinary(int binary, int digits) {
      
        String temp = Integer.toBinaryString(binary);
        int foundDigits = temp.length();
        String returner = temp;
        for (int i = foundDigits; i < digits; i++) {
            returner = "0" + returner;
        }
      
        return returner;
    } 

	
	
	
	/* ####################################################### B END ################################################ */
	
	/* ####################################################### C START ############################################## */
	
	private class ProductState extends State{
		State ltsState;
		Expression<Boolean> tformState;
		TFormula finalstate;
		NBA nba;
		//boolean visited;
		StoredState storedState;
		ArrayList<ProductState> pre;
		ArrayList<ProductState> succ;
		ArrayList<Transition> trans;
		
			
		public ProductState(NBA nba,State LTS_State, StoredState sS, TFormula TForm, Proposition final_state) {
			ltsState = LTS_State;
			storedState = sS;
			tformState = nba.apMap.get(sS.getStateId());
			//visited = false;
			this.nba = nba;
			pre = new ArrayList<ProductState>();
			succ = new ArrayList<ProductState>();
			trans = new ArrayList<Transition>();
			
			if (!storedState.getAccSignature().isEmpty()) {
				finalstate=final_state;
//				System.out.println("a final State"+finalstate);
			}
			else {
				finalstate= new TFormula.Not(final_state);
//				System.out.println("not a final State" + finalstate);
			}
		}
		
		/*
		public ArrayList<ProductState> getPredecessor(){
			return pre;
		}
		
		public ArrayList<ProductState> getSuccessor(){
			return succ;
		}
		
		public ArrayList<Transition> getTransitions(){
			return trans;
		}*/
		
		//e.g. r -> g , g -> r example lecture
		public Action canTransition(ProductState destination) {
			Iterator<Transition> it = ltsState.iterator();
			while(it.hasNext()) {
				Transition tr = it.next();
				if (tr.target.equals(destination.ltsState)) { // r --a-> g
					//ss --g-> dest.ss ?
					 Iterator<StoredEdgeWithLabel> it2 = nba.aut.getEdgesWithLabel(storedState.getStateId()).iterator();
					 while (it2.hasNext()) {
						 StoredEdgeWithLabel nx = it2.next();
						 if (nx.getConjSuccessors().contains(destination.storedState.getStateId())) { // ss ---> dest.ss
							 Proposition xy = nba.propOfLabel(nx.getLabelExpr()); 
							 if (destination.ltsState.satisfies(xy)) { //Richtig?
								 return tr.action;
							 }							 
						 }
					 }					
				}				
			}			
			return null;
		}
		

		@Override
		public Iterator<Transition> iterator() {
			return trans.iterator();
		}

		@Override
		public boolean satisfies(Proposition prop) {
//			System.out.println("Hsssssssssssssss" + finalstate.equals(prop) + "fs" + finalstate + " p" + prop);
			return finalstate.equals(prop);
		
		
		}
		
		@Override
		public String toString() {
			return "("+ltsState+" ;; "+tformState+")";
		}

		public void initTransitions(Collection<ProductState> products) {
			for (ProductState prod : products) {
				Action act = canTransition(prod);
				if (act != null){
					System.out.println(act);
					trans.add(new Transition(act,prod));
					succ.add(prod);
					prod.addPre(this);
				}
				//NEUEUUEUEEUEEUEU
				else {
					//if no final state before
					if(true){
						//trans.add(new Transition(new Action("true"),sink));
						//succ.add(sink);
						//sink.addPre(this);						
					}
				}
			}
			
		}

		private void addPre(ProductState productState) {
			if (!pre.contains(productState)) {
				pre.add(productState);
			}
			
		}
		
	}
	
	private class ProductLTS extends LTS{
		LTS model;
		TFormula tform;
		NBA nba;
		Proposition prop;
		//Collection <ProductState> initialStates;
		
		/**
		 * 
		 * @param model LTS model
		 * @param tform TFormula
		 * @throws NotSupportedFormula if Tformula is not valid LTL and translation to NBA fails.
		 */
		public ProductLTS(LTS model,TFormula tform, Proposition Prop) throws NotSupportedFormula {
			super();
			prop=Prop;
			this.model = model;
			this.tform = tform;
			TFormula tform2= new TFormula.Not(tform);
			this.nba = new NBA(tform2);
			initialStates = new ArrayList<State>();
			Collection<ProductState> products = productStates();
			createLTS(products);
			//SEE BELOW 
			
			this.initialStates=getInitStates(products);			
			
//			System.out.println("InitialStates" + initialStates.size());
			
//			printStates(products);
//			System.out.println("got "+products.size());
//			System.out.println("should have: "+getSize(nba)+"*"+getSize(model) +"(="+getSize(nba)*getSize(model)+")");
		}
		
		
		

		private Collection<State> getInitStates(Collection<ProductState> products) {
			ArrayList<State> InitStates =new ArrayList<State>();
			for (ProductState state: products) {
				if (model.initialStates.contains(state.ltsState)) {
					
					if (nba.aut.getStoredHeader().getStartStates().size()>1) System.out.println("falsche Annahme. Muss geändert werden");
					
					Iterator<Integer> it = nba.aut.getStoredHeader().getStartStates().get(0).iterator();
					
					
					while (it.hasNext()) {
					 Iterator<StoredEdgeWithLabel> it2 = nba.aut.getEdgesWithLabel(it.next()).iterator();
					
					 while (it2.hasNext()) {
						 StoredEdgeWithLabel nx = it2.next();
						 if (nx.getConjSuccessors().contains(state.storedState.getStateId())) { // ss ---> dest.ss
							 Proposition xy = nba.propOfLabel(nx.getLabelExpr()); 
							 if (state.ltsState.satisfies(xy)) { 
								 InitStates.add(state);
							 }							 
						 }
					 }	
					 
					}
					
				}
			}			
			return InitStates;
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
				prod.initTransitions(products);
			}
		}
			
		

		
		private Collection<ProductState> productStates() {
			Iterator<State> it = model.iterator();
			Collection<ProductState> prods = new ArrayList<ProductState>();
			
			while (it.hasNext()) {
				State ltsState = it.next();
				Iterator<StoredState>  tf =  nba.aut.getStoredStates().iterator();
				while (tf.hasNext()) {
					StoredState n =  tf.next();
					prods.add(new ProductState(nba,ltsState, n, tform, prop));					
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
		ProductLTS productLTS = new ProductLTS(model,tform, af);
		return productLTS; 
	}
	
	
	public int getSize(NBA nba2) {
		Iterator<StoredState> it = nba2.aut.getStoredStates().iterator();
		int c = 0;
		while(it.hasNext()) {
			it.next();
			c++;
		}
		
		return c;
	}

	public int getSize(LTS model2) {
		Iterator<State> it = model2.iterator();
		int c = 0;
		while(it.hasNext()) {
			it.next();
			c++;
		}
		
		return c;
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
			 new NBA(tform);
		}
		catch (NotSupportedFormula e) {
			return false; //tform is no valid ltl formula			
		}
		
		
		LTS productLTS=null;
		Expression<Boolean> bexpr = new BoolVariable("F");
		TFormula.Proposition af = new TFormula.Proposition(bexpr); //how to get actual af? 
		
		
		
		//Do we need to do this or is the corresponding tform given in the tests?
		TFormula a = new TFormula.Proposition(new BoolVariable("a"));
		TFormula b = new TFormula.Proposition(new BoolVariable("b"));
		TFormula z = new TFormula.Proposition(new BoolVariable("z"));
		
		
		TFormula suba = new TFormula.Until(a, z);
		TFormula subb = new TFormula.Until(b, z);
		
		
		TFormula ph = new TFormula.And(suba, subb);
		
//		System.out.println(ph);
		System.out.println("Size of blackbox NBA: "+nbStatesBb(ph));
		System.out.println("Size of 'closure' translation: "+nbStatesCl(tform));
		
		////
		
		try {
			productLTS = product(model, tform, af);
		} catch (NotSupportedFormula e) {
			return false;
		}
		

		LinkedList<State> wit = (LinkedList<State>) persistenceWit(productLTS, af, bound);
		//System.out.println("Wit" + wit);
		if (wit == null) {
			//System.out.println("Wittter");	
			return true;
		} 
		
		return false;
		
	}

}
