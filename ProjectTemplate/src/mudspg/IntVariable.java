package mudspg;

public class IntVariable extends Variable<Integer> {

	
	public IntVariable(String vname) {
		name = vname;
		initial = new Constant<Integer>(0);
	}
	
	public IntVariable(String vname, Expression<Integer> x) {
		name = vname;
		initial = x;
	}
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "(int)" + name;
	}

	@Override
	public Integer compute(Evaluation e) {
		// TODO Auto-generated method stub
		return e.get_int(this);
	}
	
}
