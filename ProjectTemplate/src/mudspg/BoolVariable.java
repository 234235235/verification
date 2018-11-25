package mudspg;

/**
 * A boolean variable
 * @author dstan
 *
 */
public class BoolVariable extends Variable<Boolean> {
	
	public BoolVariable(String vname) {
		name = vname;
		initial = new Constant<Boolean>(false);
	}
	
	public BoolVariable(String vname, Expression<Boolean> x) {
		name = vname;
		initial = x;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(bool)" + name;
	}

	@Override
	public Boolean compute(Evaluation e) {
		// TODO Auto-generated method stub
		return e.get_bool(this);
	}

}
