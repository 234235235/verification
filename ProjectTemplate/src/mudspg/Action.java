package mudspg;

/**
 * Action of a program graph, may have a label
 * @author dstan
 *
 */
public class Action {

	String label;
	
	public Action(String clabel) {
		label = clabel;
	}
	
	// Some hardcoded labels
	static public Action tau = new Action("tau");
	static public Action breakloop = new Action("bl");
	static public Action abort = new Action("abort");

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		switch(label) {
		case "tau":
			return "tau";
		case "abort":
			return "abort";
		case "bl":
			return "bl";
		default:
			return label;
		}
	}
	
	
}
