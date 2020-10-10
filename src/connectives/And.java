/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import concepts.ConceptExpression;
import formula.Formula;
import individual.Individual;
import roles.RoleExpression;

import java.util.HashSet;
import java.util.List;

/**
 *
 * @author Yizheng
 */
public class And extends Formula {

	public And() {
		super();
	}
	
	public And(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
		this.c_sig = new HashSet<>();
		this.r_sig = new HashSet<>();
		for (Formula conjunct : list) {
			this.set_c_sig(conjunct.get_c_sig());
			this.set_r_sig(conjunct.get_r_sig());	
		}
	}

	/*
	public Set<AtomicConcept> get_c_sig() {
		List<Formula> conjunct_list = this.getSubFormulas();
		Set<AtomicConcept> ac_set = new HashSet<>();
		for (Formula conjunct : conjunct_list) {
			ac_set.addAll(conjunct.get_c_sig());
		}
		return ac_set;
	}
	
	public Set<AtomicRole> get_r_sig() {
		List<Formula> conjunct_list = this.getSubFormulas();
		Set<AtomicRole> ar_set = new HashSet<>();
		for (Formula conjunct : conjunct_list) {
			ar_set.addAll(conjunct.get_r_sig());
		}
		return ar_set;
	}
*/
	@Override
	public String toString() {
		if (this.getSubFormulas().size() == 1) {
			return this.getSubFormulas().get(0).toString();
		}
		String str = "";
		for (int i = 0; i < this.getSubFormulas().size(); i++) {
			if (i == 0) {
				if (this.getSubFormulas().get(i) instanceof ConceptExpression
						|| this.getSubFormulas().get(i) instanceof RoleExpression
						|| this.getSubFormulas().get(i) instanceof Individual
						|| this.getSubFormulas().get(i) instanceof Negation
						|| this.getSubFormulas().get(i) instanceof Exists
						|| this.getSubFormulas().get(i) instanceof Forall) {
					str = str + this.getSubFormulas().get(i);
					continue;
				}
				str = str + "(" + this.getSubFormulas().get(i) + ")";
				continue;
			}
			if (this.getSubFormulas().get(i) instanceof ConceptExpression
					|| this.getSubFormulas().get(i) instanceof RoleExpression
					|| this.getSubFormulas().get(i) instanceof Individual
					|| this.getSubFormulas().get(i) instanceof Negation
					|| this.getSubFormulas().get(i) instanceof Exists
					|| this.getSubFormulas().get(i) instanceof Forall) {
				str = str + " \u2293 " + this.getSubFormulas().get(i);
				continue;
			}
			str = str + " \u2293 " + "(" + this.getSubFormulas().get(i) + ")";
		}
		return str + "";
	}
}
