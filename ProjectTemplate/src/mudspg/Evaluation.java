/**
 * 
 */
package mudspg;

import java.util.Collection;
import java.util.Map;
import java.util.Hashtable;

/**
 * An evaluation, giving for each Variable its current value, for typing reasons, boolean and
 * integral variables are given separetely.
 * @author dstan
 *
 */
public class Evaluation {
	protected Map<Variable<Integer>, Integer> int_values;
	protected Map<Variable<Boolean>, Boolean> bool_values;
	
	public Evaluation() {
		super();
		int_values = new Hashtable<Variable<Integer>, Integer>();
		bool_values = new Hashtable<Variable<Boolean>, Boolean>();
	}
	
	public Evaluation(Map<Variable<Integer>, Integer> int_values, Map<Variable<Boolean>, Boolean> bool_values) {
		super();
		this.int_values = new Hashtable<Variable<Integer>, Integer>(int_values);
		this.bool_values = new Hashtable<Variable<Boolean>, Boolean>(bool_values);
	}
	
	/**
	 * Create a new evaluation with default values
	 * @param ivar
	 * @param bvar
	 */
	public Evaluation(Collection<Variable<Integer>> ivar, Collection<Variable<Boolean>> bvar){
		super();
		int_values = new Hashtable<Variable<Integer>, Integer>();
		bool_values = new Hashtable<Variable<Boolean>, Boolean>();
		for(Variable<Integer> v: ivar) {
			int_values.put(v, v.initial.compute(this));
		}
		for(Variable<Boolean> v: bvar) {
			bool_values.put(v, v.initial.compute(this));
		}
	}
	
	public int get_int(Variable<Integer> v) {
		return int_values.get(v);
	}
	
	public void set_int(Variable<Integer> v, int new_value) {
		int_values.put(v, new_value);
	}
	
	public boolean get_bool(Variable<Boolean> v) {
		return bool_values.get(v);
	}
	
	public void set_bool(Variable<Boolean> v, boolean new_value) {
		bool_values.put(v, new_value);
	}
	
	/**
	 * 
	 * @return a fresh copy of the evaluation
	 */
	public Evaluation copy() {
		return new Evaluation(int_values, bool_values);
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((bool_values == null) ? 0 : bool_values.hashCode());
		result = prime * result
				+ ((int_values == null) ? 0 : int_values.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof Evaluation)) {
			return false;
		}
		Evaluation other = (Evaluation) obj;
		if (bool_values == null) {
			if (other.bool_values != null) {
				return false;
			}
		} else if (!bool_values.equals(other.bool_values)) {
			return false;
		}
		if (int_values == null) {
			if (other.int_values != null) {
				return false;
			}
		} else if (!int_values.equals(other.int_values)) {
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String res = "[";
		String last = "";
		for(Map.Entry<Variable<Integer>, Integer> entry: int_values.entrySet()) {
			res += last;
			res += entry.getKey().toString() + "=" + entry.getValue();
			last = ",";
		}
		for(Map.Entry<Variable<Boolean>, Boolean> entry: bool_values.entrySet()) {
			res += last;
			res += entry.getKey().toString() + "=" + entry.getValue();
			last = ",";
		}
		return res + "]";
	}
	
}
