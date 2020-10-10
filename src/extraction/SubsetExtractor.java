package extraction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;

public class SubsetExtractor {

	public SubsetExtractor() {

	}
	
	public Set<AtomicConcept> getConceptsFromFormula(Formula formula) {
		
		Set<AtomicConcept> concept_set = new HashSet<>();
		
		if (formula instanceof AtomicConcept) {
			AtomicConcept concept = (AtomicConcept) formula;
			concept_set.add(concept);
			
		} else if (formula instanceof Exists) {
			concept_set.addAll(getConceptsFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof Inclusion) {		
			concept_set.addAll(getConceptsFromFormula(formula.getSubFormulas().get(0)));
			concept_set.addAll(getConceptsFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				concept_set.addAll(getConceptsFromFormula(operand));
			}
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesFromFormula(Formula formula) {
		
		Set<AtomicRole> role_set = new HashSet<>();
		
		if (formula instanceof AtomicRole) {
			AtomicRole role = (AtomicRole) formula;
			role_set.add(role);
			
		} else if (formula instanceof Exists) {
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof Inclusion) {		
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(0)));
			role_set.addAll(getRolesFromFormula(formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> operand_list = formula.getSubFormulas();
			for (Formula operand : operand_list) {
				role_set.addAll(getRolesFromFormula(operand));
			}			
		}

		return role_set;
	}
	
	public List<Formula> getConceptSubset(AtomicConcept concept, List<Formula> formula_list) {
		
		List<Formula> output_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicConcept> c_set = formula.get_c_sig();
			if (c_set.contains(concept)) {
				System.out.println("pivot concept = " + formula);
				System.out.println("Formula 1 [" + i + "] = " + formula);
				output_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return output_list;
	}
		
	public List<Formula> getConceptSubset(Set<AtomicConcept> c_sig, List<Formula> formula_list) {

		List<Formula> c_sig_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicConcept> c_set = formula.get_c_sig();
			if (!Sets.intersection(c_set, c_sig).isEmpty()) {
				c_sig_list.add(formula);
				formula_list.remove(i);
				i--;
			}
			System.out.println("Formula 2 [" + i +"] = " + formula);
		}
		return c_sig_list;
	}
		
	public List<Formula> getRoleSubset(AtomicRole role, List<Formula> formula_list) {

		List<Formula> role_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicRole> r_set = formula.get_r_sig();
			if (r_set.contains(role)) {
				System.out.println("pivot role = " + role);
				System.out.println("Formula 3 [" + i +"] = " + formula);
				role_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return role_list;
	}
	
	public List<Formula> getRoleSubset(Set<AtomicRole> r_sig, List<Formula> formula_list) {

		List<Formula> r_sig_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicRole> r_set = formula.get_r_sig();
			if (!Sets.intersection(r_set, r_sig).isEmpty()) {
				r_sig_list.add(formula);
				formula_list.remove(i);
				i--;
			}
			System.out.println("Formula 4 [" + i +"] = " + formula);
		}

		return r_sig_list;
	}

}
