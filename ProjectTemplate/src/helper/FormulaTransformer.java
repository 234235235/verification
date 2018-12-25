package helper;

import mudspg.TFormula;
import mudspg.TFormula.*;

public abstract class FormulaTransformer<T> {
	public T process(TFormula f)  throws NotSupportedFormula  {
		if(f instanceof Exist)
			return exist((Exist) f);
		if(f instanceof All)
			return all((All) f);
		if(f instanceof Not)
			return not((Not) f);
		if( f instanceof Next)
			return next((Next) f);
		if(f instanceof Globally)
			return globally((Globally) f);
		if(f instanceof Eventually)
			return eventually((Eventually) f);
		if(f instanceof Until)
			return until((Until) f);
		if(f instanceof WeakUntil)
			return weakUntil((WeakUntil) f);
		if(f instanceof And)
			return and((And) f);
		if(f instanceof Or)
			return or((Or) f);
		if(f instanceof Proposition)
			return proposition((Proposition) f);

		return unsupported(f);
	}
	
	abstract protected T exist(Exist f)  throws NotSupportedFormula ;
	abstract protected T all(All f)  throws NotSupportedFormula ;
	abstract protected T next(Next f)  throws NotSupportedFormula ;
	abstract protected T not(Not f)  throws NotSupportedFormula ;
	abstract protected T globally(Globally f)  throws NotSupportedFormula ;
	abstract protected T eventually(Eventually f)  throws NotSupportedFormula ;
	abstract protected T until(Until f)  throws NotSupportedFormula ;
	abstract protected T weakUntil(WeakUntil f)  throws NotSupportedFormula ;
	abstract protected T and(And f)  throws NotSupportedFormula ;
	abstract protected T or(Or f)  throws NotSupportedFormula ;
	abstract protected T proposition(Proposition f)  throws NotSupportedFormula ;
	protected T unsupported(TFormula f) throws NotSupportedFormula {
		throw new NotSupportedFormula();
	}
}
