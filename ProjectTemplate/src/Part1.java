import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Set;

import org.antlr.v4.runtime.misc.Pair;

import mudschecker.*;
import mudspg.Constant;
import mudspg.TFormula;
import mudspg.TFormula.All;
import mudspg.TFormula.BinaryOp;
import mudspg.TFormula.Eventually;
import mudspg.TFormula.Exist;
import mudspg.TFormula.Globally;
import mudspg.TFormula.Next;
import mudspg.TFormula.UnaryOp;
import mudspg.TFormula.Until;
import mudspg.TFormula.WeakUntil;

import java.util.HashSet;
import java.util.Iterator;


public class Part1 extends AbstractChecker {
	private ArrayList<Class<?>> sf_final = new ArrayList<Class<?>>(Arrays.asList(TFormula.Proposition.class));
	private ArrayList<Class<?>> sf_path = new ArrayList<Class<?>>(Arrays.asList(TFormula.All.class, TFormula.Exist.class));
	private ArrayList<Class<?>> sf_sf = new ArrayList<Class<?>>(Arrays.asList(TFormula.Not.class,TFormula.And.class,TFormula.Or.class));
	
	private ArrayList<Class<?>> sf = new ArrayList<Class<?>>() { {addAll(sf_final); addAll(sf_path); addAll(sf_sf); }};
	
	private ArrayList<Class<?>> enf_classes = new ArrayList<Class<?>>(Arrays.asList(TFormula.And.class,TFormula.Not.class,TFormula.Exist.class,
			TFormula.Next.class,TFormula.Until.class,TFormula.Globally.class,TFormula.Proposition.class,TFormula.Or.class));
	/* ###################################################################checkBounded #####################################################################*/
	/**
	 * Exercise: given a model and a bound, does the model has less than n states ?
	 * @param model
	 * @param bound
	 * @return
	 */
	public boolean checkBounded(LTS model, int bound) {
		System.out.println("checkBounded");	
		int count = 0;
		Iterator<State> it = model.iterator();
		while (it.hasNext()) {
			it.next();
			count++;
			if (count >= bound) {
				return false;
			}
		}
		System.out.println("Got "+count+" states!"); //c+"("+count+") states!");
		System.out.println("--------------");
		return count < bound; 
	}	
	/* ###############################################################################################################################################*/
	
	/* ###################################################################isCTL? #####################################################################*/
	
	/**
	 * @return boolean is the formula a CTL formula ?
	 */
	/* state formulas sf = true | a | sf1 && sf2 | sf1 || sf2 | !sf | E pf | A pf
	 * path formulas pf = X sf | sf1 U sf2 | F sf | G sf | sf1 W sf2
	 * */
	public boolean isCTL(TFormula phi) {
		//ASSUMPTION: CTL can start wiht state and path formula
			
		boolean res;
		if (sf.contains(phi.getClass())) res =  isStateFormula(phi);
		else res =  isPathFormula(phi);
		
		System.out.println("isCTL? "+res+"! "+phi);
		return res;
	}
	
	// state formulas sf = true | a | sf1 && sf2 | !sf | E pf | A pf
	/**
	 * @return boolean is the formula a State formula ?
	 */
	private boolean isStateFormula(TFormula phi) {	
		if (sf_final.contains(phi.getClass())) {
//			System.out.println("isStateFormula? "+phi.getClass()+": "+phi+"\n"+true+"\n -----------------------");
			return true;
		}
		else if (sf_path.contains(phi.getClass())) {
//			System.out.println("isStateFormula? "+phi.getClass()+": "+phi+"\n"+true+"\n -----------------------");
			return isPathFormula(getSubFormula(phi));
			
		}
		else if (sf_sf.contains(phi.getClass())) {
//			System.out.println("isStateFormula? "+phi.getClass()+": "+phi+"\n"+true+"\n -----------------------");
			return isStateFormula(getSubFormula(phi));
			
		}
//		System.out.println("isStateFormula_fail? "+phi.getClass()+": "+phi+"\n"+false+"\n -----------------------");
		return false;
	}
	
	/**
	 * @return are all formulas state formulas?
	 */
	private boolean isStateFormula(ArrayList<TFormula> subFormula) {
		boolean res = true;
//		System.out.println(subFormula.size());
		for (TFormula t : subFormula) {
			res = res && isStateFormula(t);
		}
		return res;
	}

	/**
	 * @return returns a list of subformulas (binary: 2 items, unary 1 item)
	 */
	private ArrayList<TFormula> getSubFormula(TFormula phi) {
		if (phi instanceof UnaryOp) {
			return new ArrayList<TFormula>(Arrays.asList(((UnaryOp) phi).sub));
		}
		else if (phi instanceof BinaryOp) {
			return new ArrayList<TFormula>(Arrays.asList(((BinaryOp) phi).suba,((BinaryOp) phi).subb));
		}
		return new ArrayList<TFormula>();
	}

	
	private boolean isPathFormula(ArrayList<TFormula> arrayList) {
		boolean res = true;
//		System.out.println(arrayList.size());
		for (TFormula t : arrayList) {
			res = res && isPathFormula(t);
		}
		return res;
		
	}
	
	// path formulas pf = X sf | sf1 U sf2 | F sf | G sf | sf1 W sf2
	 
	private boolean isPathFormula(TFormula phi) {
		//ASSUMPTION: Weak until of type sf1 W sf2
		if (sf.contains(phi.getClass())) {
//			System.out.println("isPathFormula? false! "+phi.getClass()+", "+phi+"\n"+"\n -----------------------");
			return false;
		}
//		System.out.println("isPathFormula? true! s"+phi.getClass()+", "+phi+"\n"+"\n -----------------------");
		return isStateFormula(getSubFormula(phi));
		
	}
	/* ###############################################################################################################################################*/
	
	/* ###################################################################toENF #####################################################################*/
	private Pair<ArrayList<TFormula>,String> getSubFormula_2(TFormula phi) {
		if (phi instanceof UnaryOp) {
			return new Pair<ArrayList<TFormula>,String>(new ArrayList<TFormula>(Arrays.asList(((UnaryOp) phi).sub)),phi.getClass().getSimpleName());
		}
		else if (phi instanceof BinaryOp) {
			return new Pair<ArrayList<TFormula>,String>(new ArrayList<TFormula>(Arrays.asList(((BinaryOp) phi).suba,((BinaryOp) phi).subb)),phi.getClass().getSimpleName());
		}
		return new Pair<ArrayList<TFormula>,String>(new ArrayList<TFormula>(),"empty");
	}
	
	/**
	 * Exercise: given a temporal formula, construct its ENF, or raise an Exception
	 * @throws Exception 
	 */
	//ASSUMPTION: need to translate: (state) A; (path) W, F
	//ASSUMPTION: OR is in ENF!	
	public TFormula toENF(TFormula phi) throws Exception {
		phi = getENF(phi);
		if (!isENF(phi)){
			throw new Exception("Could not convert to ENF! "+phi);
		}
		return phi;
		
	}	
	
	public TFormula getENF(TFormula phi) {
//		System.out.println("CURR: "+phi);
		if(getSubFormula(phi).isEmpty()) {
//			System.out.println("subempty!");
			return single_toENF(phi);
		}
//		System.out.println("sub not empty!");
		
		ArrayList<TFormula> res = new ArrayList<TFormula>();
		Pair<ArrayList<TFormula>,String> p  = getSubFormula_2(phi);
		
		
		for (TFormula t : p.a) {
			res.add(getENF(t));
		}
		
		TFormula x = combine(res,p.b);
		System.out.println("CURRENT: "+x);
		x = single_toENF(x);
		System.out.println("TOENF_RES: "+x);
		return single_toENF(combine(res,p.b));
	}
		
	
	private void checkSize(ArrayList<TFormula> res,int s,String b) {
		if(res.size() > s) {
			System.out.println("S.th went fking wrong: "+b+" , "+res);
		}
	}
	
	/**
	 * 
	 * @param res the corresponding items to combine
	 * @param b the string value of getClass().getSimpleName()
	 * @return e.g. res = [(int)x==C(10)], b = Next -> X [[(int)x==C(10)]]  
	 */
	private TFormula combine(ArrayList<TFormula> res, String b) {
		switch(b) {
		case "Exist":
			checkSize(res,1,b);
			return new TFormula.Exist(res.get(0));
		case "All":
			checkSize(res,1,b);
			return new TFormula.All(res.get(0));
		case "Next":
			checkSize(res,1,b);
			return new TFormula.Next(res.get(0));
		case "Not":
			checkSize(res,1,b);
			return new TFormula.Not(res.get(0));
		case "Globally":
			checkSize(res,1,b);
			return new TFormula.Globally(res.get(0));
		case "Eventually":
			checkSize(res,1,b);
			return new TFormula.Eventually(res.get(0));
		case "Until":
			checkSize(res,2,b);
			return new TFormula.Until(res.get(0), res.get(1));
		case "WeakUntil":
			checkSize(res,2,b);
			return new TFormula.WeakUntil(res.get(0), res.get(1));
		case "And":
			checkSize(res,2,b);
			return new TFormula.And(res.get(0), res.get(1));
		case "Or":
			checkSize(res,2,b);
			return new TFormula.Or(res.get(0), res.get(1));
		
			
		default:
			System.out.println("SWITCHFAIL "+b+", "+res);
			break;
		}
		return null;
	}
	
	private TFormula combine_Back(TFormula phi, int notCount) {
		while (notCount > 0) {
			ArrayList<TFormula> xy = new ArrayList<TFormula>();
			xy.add(phi);
			phi = combine(xy, "Not");
			notCount--;
		}
		return phi;
	}
	/**
	 * 
	 * @param phi
	 * @return returns phi with most outer form translated to ENF
	 * @throws Exception
	 */
	public TFormula single_toENF(TFormula phi) {
		int notCount = 0;
		
		while (!curr_subs_isENF(phi)) {
			while (phi instanceof TFormula.Not) {
				phi = ((TFormula.Not)phi).sub;
				notCount++;
			
			}
			//System.out.println("CURR_toENF:"+phi);
			if (phi instanceof Exist) {// E bla
				TFormula sub1 = ((Exist) phi).sub;
				//transform: E F phi -> E (true U phi)
				if (sub1 instanceof Eventually) { //E F bla
					TFormula sub2 = ((Eventually) sub1).sub; //E F sub2
					TFormula suba = new TFormula.Proposition(Constant.true_value); //true
					TFormula ed = new TFormula.Until(suba, sub2); //(true U sub2)
					phi = new TFormula.Exist(ed);	//E (true U sub2)
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
				//transform: E(phi1 W phi2) -> E(phi1 U phi2) || E G phi1
				//ASSUMPTION: We can use the equivalenz on lect5 slide 15
				if(sub1 instanceof WeakUntil) { //E (bla W bla)
					TFormula sub2a = ((WeakUntil) sub1).suba; // E (sub2a W bla)
					TFormula sub2b = ((WeakUntil) sub1).subb; // E (sub2a W sub2b)
					
					TFormula ed2a = new TFormula.Until(sub2a, sub2b); //(sub2a U sub2b)
					TFormula ed1a = new TFormula.Exist(ed2a); // E (sub2a U sub2b)
				
					TFormula ed2b = new TFormula.Globally(sub2a);//G sub2a
					TFormula ed1b = new TFormula.Exist(ed2b);//E G sub2a
					
					phi = new TFormula.Or(ed1a, ed1b); //(E (sub2a U sub2b)) v (E G sub2a)
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
			}
			if (phi instanceof All) {// A bla
				TFormula sub1 = ((All)phi).sub;
				//transform: A F phi -> A(true U phi)
				if (sub1 instanceof Eventually) { // A F bla
					TFormula sub2 = ((Eventually) sub1).sub; //A F sub2
					TFormula suba = new TFormula.Proposition(Constant.true_value); //true
					TFormula ed = new TFormula.Until(suba, sub2); // (true U sub2)
					phi = new TFormula.All(ed); //A (true U sub2)
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
				if(sub1 instanceof WeakUntil) { //A (bla W bla)
					TFormula sub2a = ((WeakUntil) sub1).suba; // A (sub2a W bla)
					TFormula sub2b = ((WeakUntil) sub1).subb; // A (sub2a W sub2b)
					
					TFormula ed4ab = new TFormula.Not(sub2b); //!sub2b
					TFormula ed3a = new TFormula.And(sub2a, ed4ab); //(sub2a && !sub2b)
					
					TFormula ed4bb = new TFormula.Not(sub2b); //!sub2b
					TFormula ed4ba = new TFormula.Not(sub2a); //!sub2a
					
					TFormula ed3b = new TFormula.And(ed4ba, ed4bb);//(!sub2a && !sub2b )
					
					TFormula ed2 = new TFormula.Until(ed3a, ed3b);//((sub2a && !sub2b) U (!sub2a && !sub2b ))
					TFormula ed1 = new TFormula.Exist(ed2); //E ((sub2a && !sub2b) U (!sub2a && !sub2b ))
							
					phi = new TFormula.Not(ed1); // !E ((sub2a && !sub2b) U (!sub2a && !sub2b ))
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
				
				
				//transform: A G phi -> !(E (F !phi))
				if(sub1 instanceof Globally) {//A G bla
					TFormula sub2 = ((Globally) sub1).sub; //A G sub2
					TFormula ed3 = new TFormula.Not(sub2); // !sub2
					TFormula ed2 = new TFormula.Eventually(ed3); //F !sub2
					TFormula ed1 = new TFormula.Exist(ed2); // E F !sub2
					phi = new TFormula.Not(ed1); // !(E (F(!sub2)))
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
				//transform: A X phi -> !(E (X !phi))
				if(sub1 instanceof Next) { //A X bla
					TFormula sub2 = ((Next)sub1).sub; //A X sub2
					TFormula ed3 = new TFormula.Not(sub2); //!sub2
					TFormula ed2 = new TFormula.Next(ed3); //X !sub2
					TFormula ed1 = new TFormula.Exist(ed2);//E X !sub2
					phi = new TFormula.Not(ed1); //!(E (X ! sub2))
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
				//transform A (phi1 U phi2) -> !E(!phi2 U (!phi1 && !phi2)) && !E A !phi2
				//ASSUMPTION: and bindet stärker als Exist: E a && b = (E (a &&b))
				if (sub1 instanceof Until) { // A ( bla U bla)
					TFormula sub2a = ((Until)sub1).suba; //A (sub2a U bla)
					TFormula sub2b = ((Until)sub1).subb; //A (sub2a U sub2b)
					
					TFormula ed4aa = new TFormula.Not(sub2b); //!sub2b
					
					TFormula ed5aba = new TFormula.Not(sub2a); //!sub2a 
					TFormula ed5abb = new TFormula.Not(sub2b); //!sub2b
					
					TFormula ed4ab = new TFormula.And(ed5aba, ed5abb);// (!sub2a && !sub2b)
									
					TFormula ed3a = new TFormula.Until(ed4aa, ed4ab); //(!sub2b U (!sub2a && sub2b))
					
					TFormula ed6b = new TFormula.Not(sub2b); // !sub2b
					TFormula ed5b = new TFormula.Globally(ed6b); //G !sub2b
					TFormula ed4b = new TFormula.Exist(ed5b);// E (G !sub2b)
					TFormula ed3b = new TFormula.Not(ed4b); // ! (E (G !sub2b))
					
					TFormula ed2 = new TFormula.And(ed3a, ed3b); // (!sub2b U (!sub2a && sub2b)) && !(E (G !sub2b))
					TFormula ed1 = new TFormula.Exist(ed2); //E ((!sub2b U (!sub2a && sub2b)) && !(E (G !sub2b)))
					phi = new TFormula.Not(ed1); //!E ((!sub2b U (!sub2a && sub2b)) && !(E (G !sub2b)))	
					
					phi = combine_Back(phi,notCount);
					notCount = 0;
					
					continue;
				}
			}
			//ERROR phi is not in enf, but can't also be converted any further...
			//throw new Exception("Can not convert to ENF: "+phi.getClass()+": "+phi);
			phi = combine_Back(phi,notCount);
			notCount = 0;
			
			break;
		}
		return phi;
	}
	
	private boolean subs_isENF(TFormula phi) {
		ArrayList<TFormula> subs = getSubFormula(phi);
		boolean res = true;
		for (TFormula t : subs) {
			res = res && curr_isENF(t);
		}
		return res;
	}
	private boolean curr_subs_isENF(TFormula phi) {
		while (phi instanceof TFormula.Not) {
			phi = ((TFormula.Not) phi).sub;
		}
		return curr_isENF(phi) && subs_isENF(phi);
	}
	private boolean curr_isENF(TFormula phi) {
		if (enf_classes.contains(phi.getClass())) {
			return true;
		}
		return false;
	}
	
	
	private boolean isENF(TFormula phi) {
		ArrayList<TFormula> list = new ArrayList<TFormula>();
		list.add(phi);
		while (!list.isEmpty()) {
			ArrayList<TFormula> newList = new ArrayList<TFormula>();			
			boolean all_enf = true;
			
			for (TFormula item : list) {
				boolean curr = curr_isENF(item);
				if (!curr) {
					System.out.println("~~~This is no ENF!~~~");
					System.out.println(phi);
					System.out.println(".."+item);
					System.out.println("~~~~~~~~~~~~~~~~~~~~~");
				}
				all_enf = all_enf && curr;
				newList.addAll(getSubFormula(item));
			}
			
			if (!all_enf) {
				return false;
			}
			list = newList;
		}
		return true;
	}
	
	/* #############################################################################################################################################*/
	
	

	/**
	 * Exercise: given a finite model and a temporal formula in ENF, returns the satisfaction set.
	 * Any implementation of Set<State> is allowed (but choose carefully)
	 */
	public Set<State> satSet(LTS model, TFormula phi) {
		if(phi instanceof TFormula.Proposition) 
			return satSetProp(model, (TFormula.Proposition) phi);
		// Write the rest !
		return Collections.emptySet();
	}
	
	/** 
	 * As a courtesy, and in order to provide an example of the API use, we offer you a solution
	 * for the sat. set of a proposition.
	 * @param model
	 * @param phi
	 * @return
	 */
	protected Set<State> satSetProp(LTS model, TFormula.Proposition phi) {
		Set<State> res = new HashSet<State>();
		for(State s: model) {
			if(s.satisfies(phi))
				res.add(s);
		}
		return res;
	}
	
	/**
	 * Exercise: wrap it together
	 */
	@Override
	public boolean solve(LTS model, TFormula tform, int bound) {
		
		
		if (!checkBounded(model,bound)) {
			System.err.println("Model exceeds bound!");
			return false;
		}
		
		if(!isCTL(tform)) {
			System.err.println("This Tformular is no CTL!: \n"+tform);
		}
		
		System.out.println("toENF: "+tform);
		TFormula enf_tform;
		try {enf_tform = toENF(tform);} catch (Exception e) {System.out.println("SHIT1231245");System.out.println(e);return false;}
		
		System.out.println("FIRST RESULT: "+enf_tform);
		enf_tform = simplify(enf_tform);
		
		System.out.println("RESULT: "+enf_tform);
		
		Set<State> result = satSet(model,enf_tform);
		
		//if s0 teilmenge result -> return true else return false
		boolean isSubset = true;
		if (isSubset) return true;		
		System.out.println(model);
		System.out.println(tform);
		System.out.println(bound);
		return false;
	}
	
	
	/*########################################################################################################################################################*/
	/**
	 * @return just deletes doubled negations
	 */
	private TFormula simplify(TFormula phi) {
		if (getSubFormula(phi).isEmpty()) {
			return phi;
		}
		ArrayList<TFormula> res = new ArrayList<TFormula>();
		Pair<ArrayList<TFormula>,String> p  = getSubFormula_2(phi);
		for (TFormula t : p.a) {
			res.add(simplify(t));
		}
		
		return simplify_one(combine(res,p.b));
		
	}
	
	private TFormula simplify_one(TFormula phi) {
		if (phi instanceof TFormula.Not) {
			ArrayList<TFormula> subs = getSubFormula(phi);
			if (subs.size() == 1) {
				TFormula check = subs.get(0);
				if (check instanceof TFormula.Not) {
					ArrayList<TFormula> subssub = getSubFormula(check);
					if (subssub.size() == 1) {
						return subssub.get(0);
					}
				}
			}
		}
		return phi;		
	}


	/*########################################################################################################################################################*/
}
