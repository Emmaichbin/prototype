package extraction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import checkexistence.EChecker;
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

		EChecker ce = new EChecker();
		
		List<Formula> concept_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (ce.isPresent(concept, formula)) {
				concept_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return concept_list;
	}
		
	public List<Formula> getConceptSubset(Set<AtomicConcept> c_sig, List<Formula> formula_list) {

		//System.out.println(formula_list);
		List<Formula> c_sig_subset = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (!Sets.intersection(getConceptsFromFormula(formula), c_sig).isEmpty()) {
				c_sig_subset.add(formula);
				formula_list.remove(i);
				i--;
			}
		}
		
		formula_list.removeAll(c_sig_subset);
		
		//System.out.println(c_sig_subset);

		return c_sig_subset;
	}
		
	public List<Formula> getRoleSubset(AtomicRole role, List<Formula> formula_list) {

		EChecker ce = new EChecker();
		List<Formula> role_list = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (ce.isPresent(role, formula)) {
				role_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return role_list;
	}
	
	public List<Formula> getRoleSubset(Set<AtomicRole> r_sig, List<Formula> formula_list) {

		List<Formula> r_sig_subset = new ArrayList<>();

		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			if (!Sets.intersection(getRolesFromFormula(formula), r_sig).isEmpty()) {
				r_sig_subset.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		formula_list.removeAll(r_sig_subset);

		return r_sig_subset;
	}

}
