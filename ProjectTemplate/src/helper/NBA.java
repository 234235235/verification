package helper;


import jhoafparser.consumer.HOAConsumerException;
import jhoafparser.consumer.HOAConsumerPrint;
import jhoafparser.consumer.HOAConsumerStore;
import jhoafparser.storage.StoredAutomaton;
import jhoafparser.transformations.ToStateAcceptance;
import jhoafparser.ast.AtomLabel;
import jhoafparser.ast.BooleanExpression;

import owl.translations.ltl2ldba.LTL2LDBAFunction;
import owl.automaton.ldba.LimitDeterministicAutomaton;


import java.util.List;
import java.util.Map;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedList;

import owl.ltl.Formula;
import owl.ltl.LabelledFormula;
import static owl.translations.ltl2ldba.LTL2LDBAFunction.Configuration.EAGER_UNFOLD;                                                                                                                                                          
import static owl.translations.ltl2ldba.LTL2LDBAFunction.Configuration.FORCE_JUMPS;                                                                                                                                                           
import static owl.translations.ltl2ldba.LTL2LDBAFunction.Configuration.OPTIMISED_STATE_STRUCTURE;                                                                                                                                             
import static owl.translations.ltl2ldba.LTL2LDBAFunction.Configuration.SUPPRESS_JUMPS;

import mudspg.Evaluation;
import mudspg.Expression;
import mudspg.TFormula;
import mudspg.TFormula.All;
import mudspg.TFormula.And;
import mudspg.TFormula.Eventually;
import mudspg.TFormula.Exist;
import mudspg.TFormula.Globally;
import mudspg.TFormula.Next;
import mudspg.TFormula.Not;
import mudspg.TFormula.Or;
import mudspg.TFormula.Proposition;
import mudspg.TFormula.Until;
import mudspg.TFormula.WeakUntil;

/**
 * A NBA, constructed from a LTL formula given as an input
 * This helper is provided as is, feel free to modify/tweak it, or subclass it !
 * @author dstan
 *
 */
public class NBA extends FormulaTransformer<Formula> {
	/**
	 * The actual automaton, in JHOAFPARSER form
	 */
	public StoredAutomaton aut;
	
	/**
	 * For each ap appearing in aut, given as an integer, a corresponding muds bexpr object
	 */
	public Map<Integer, Expression<Boolean>> apMap;
	
	// internally, we need the reverse mapping
	protected HashMap<Expression<Boolean>, Integer> varMap;
	protected List<String> varNames;

	/**
	 * Construct the NBA given an (assumed) LTL formula.
	 * The implementation details are left here for completeness
	 * @param tform
	 * @throws NotSupportedFormula
	 */
	public NBA(TFormula tform) throws NotSupportedFormula {

		// Step 0: boring init
		super();
		apMap = new HashMap<Integer, Expression<Boolean>>();
		varMap = new HashMap<Expression<Boolean>,Integer>();
		varNames = new LinkedList<String>();

		// Step 1: Convert to labeled formula from Owl library (see below for the actual conversion), then to LDBA
		LabelledFormula f = LabelledFormula.of(process(tform), varNames);
		EnumSet<LTL2LDBAFunction.Configuration> opts = EnumSet.of(                                                                                                                                                                            
				 EAGER_UNFOLD, FORCE_JUMPS, OPTIMISED_STATE_STRUCTURE, SUPPRESS_JUMPS);
		
		// NB: a LDBA is a NBA with extra properties
		//LimitDeterministicAutomaton<EquivalenceClass,DegeneralizedBreakpointFreeState,BuchiAcceptance,FGObligations> automaton =
		LimitDeterministicAutomaton<?,?,?,?> automaton =
	       LTL2LDBAFunction.createDegeneralizedBreakpointFreeLDBABuilder(owl.run.DefaultEnvironment.of$15960465(true, false), opts)                                                                                                                                       
				 .apply(f);
		
		// Step 2: we have now a LDBA in owl format, export it to HOA
		HOAConsumerStore consumer = new HOAConsumerStore();
		automaton.toHoa(consumer, EnumSet.of(owl.automaton.output.HoaPrintable.HoaOption.ANNOTATIONS));
		
		// Step 3: convert to State Acceptance (owl returned a transition acceptance automaton) 
		try {
			aut = (new ToStateAcceptance()).manipulate(consumer.getStoredAutomaton());
		} catch (HOAConsumerException e) {
			// Auto-generated catch block, this should not happen on our particular automata, but Java cannot know
			e.printStackTrace();
		}

	}
	
	// Some helper functions below
	/**
	 * Return the initial state index (assumed to be only one)
	 */
	int getInitialStateIndex() {
		//StartStates are stored as disjunctions of conjunctions
		//should be only one thanks to UNFOLD_EAGER
		for(List<Integer> conj: aut.getStoredHeader().getStartStates()) {
			for( int initial: conj) {
				return (int) initial;
			}
		}
		return 0;
	}
	
	private HashMap<BooleanExpression<AtomLabel>,TFormula.Proposition> cachedPropositions = new HashMap<BooleanExpression<AtomLabel>, TFormula.Proposition>();
	/**
	 * Returns a TFormula.Proposition equivalent to a BooleanExpression<AtomLabel> that labels a transition of the NBA (cached result
	 * for efficiency).
	 * See https://automata.tools/hoa/jhoafparser/docs/javadoc/jhoafparser/ast/BooleanExpression.html
	 * @param label
	 * @return
	 */
	public TFormula.Proposition propOfLabel(BooleanExpression<AtomLabel> label) {
		if(cachedPropositions.containsKey(label))
			return cachedPropositions.get(label);
		TFormula.Proposition prop = new TFormula.Proposition(new BExprLabel(label, apMap));
		
		cachedPropositions.put(label, prop);
		return prop;
	}
	
		
	/**
	 * Print the automaton, for debugging purpose, in the HOA format
	 */
	public void printHOA() {
		// For debugging
		try {
			aut.feedToConsumer(new HOAConsumerPrint(System.out));
		} catch (HOAConsumerException e) {
			System.out.println("arg");
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	
	// Below the formula transformer part, with boring definitions.
	@Override
	protected Formula exist(Exist f) throws NotSupportedFormula {
		throw new NotSupportedFormula();
	}

	@Override
	protected Formula all(All f) throws NotSupportedFormula {
		throw new NotSupportedFormula();
	}

	@Override
	protected Formula next(Next f) throws NotSupportedFormula {
		
		return new owl.ltl.XOperator(process(f.sub));
	}

	@Override
	protected Formula not(Not f) throws NotSupportedFormula {
		return process(f.sub).not();
	}

	@Override
	protected Formula globally(Globally f)  throws NotSupportedFormula {
		return new owl.ltl.GOperator(process(f.sub));
	}

	@Override
	protected Formula eventually(Eventually f)  throws NotSupportedFormula {
		return new owl.ltl.FOperator(process(f.sub));
	}

	@Override
	protected Formula until(Until f) throws NotSupportedFormula {
		return new owl.ltl.UOperator(process(f.suba), process(f.subb));
	}

	@Override
	protected Formula weakUntil(WeakUntil f) throws NotSupportedFormula {
		return new owl.ltl.WOperator(process(f.suba), process(f.subb));
	}

	@Override
	protected Formula and(And f) throws NotSupportedFormula {

		return new owl.ltl.Conjunction(process(f.suba), process(f.subb));
	}

	@Override
	protected Formula or(Or f) throws NotSupportedFormula {
		return new owl.ltl.Disjunction(process(f.suba), process(f.subb));
	}

	// This is not part of the formula transformer (!)
	protected Formula bexpr(Expression<Boolean> bexpr) {
		int pos = 0;
		//TODO split bexpr into smaller parts. The smaller, the better.
		// Naively, we are here taking a Proposition as it is, which is bad, because
		// some propositions may be mutually exclusive. This information will be forgotten
		// once passed to the NBA builder, hence some produced transitions will be useless
		// since their label may be impossible to satisfy
		if(varMap.containsKey(bexpr)) {
			pos = varMap.get(bexpr);
		} else {
			pos = varNames.size();
			varMap.put(bexpr, pos);
			apMap.put(pos, bexpr);
			varNames.add(bexpr.toString());
		}
		return new owl.ltl.Literal(pos);
	}
	
	@Override
	protected Formula proposition(Proposition f) throws NotSupportedFormula {
		return bexpr(f.bexpr);
	}

	@Override
	protected Formula unsupported(TFormula f) throws NotSupportedFormula {
		throw new NotSupportedFormula();
	}
	
}

/** 
 * Instead of converting the whole tree of a BooleanExpression<AtomLabel> from HOAfparser, we derive
 * a new bexpr with the current label, and redefine the evaluation and toString operations
 */
class BExprLabel extends Expression<Boolean> {

	@Override
	public String toString() {
		return toString(label);
	}
	
	protected String toString(BooleanExpression<AtomLabel> label) {
		if(label.isAND())
			return "(" + toString(label.getRight()) + " && " + toString(label.getLeft()) + ")";
		if(label.isOR())
			return "(" + toString(label.getRight()) + " || " + toString(label.getLeft()) + ")";
		if(label.isNOT())
			return "!" + toString(label.getLeft());
		if(label.isTRUE()) return "true";
		if(label.isFALSE()) return "false";
		//if(label.isAtom())
		return apMap.get(label.getAtom().getAPIndex()).toString();
	}

	private BooleanExpression<AtomLabel> label;
	private Map<Integer,Expression<Boolean>> apMap;
	
	public BExprLabel(BooleanExpression<AtomLabel> label, Map<Integer, Expression<Boolean>> map) {
		super();
		this.label = label;
		apMap = map;
	}

	@Override
	public Boolean compute(Evaluation e) {
		return compute(e, label);
	}
	
	protected Boolean compute(Evaluation e, BooleanExpression<AtomLabel> label) {
		if(label.isAND())
			return compute(e, label.getRight()) && compute(e, label.getLeft());
		if(label.isOR())
			return compute(e, label.getRight()) || compute(e, label.getLeft());
		if(label.isNOT())
			return !compute(e, label.getLeft());
		if(label.isTRUE()) return true;
		if(label.isFALSE()) return false;
		//if(label.isAtom())
		return apMap.get(label.getAtom().getAPIndex()).compute(e);
	}
	
}