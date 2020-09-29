package forgetting;

import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.util.List;
import java.util.Set;


/**
 *
 * @author Yizheng
 */
public class Fame {

	public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	
	public Fame() {

	}
	
	public OWLOntology FameRC(Set<OWLObjectProperty> op_set, Set<OWLClass> c_set, OWLOntology onto)
			throws Exception {
		
		if (op_set.isEmpty() && c_set.isEmpty()) {
			return onto;
		}
		
		Converter ct = new Converter();
		Simplifier pp = new Simplifier();
		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(op_set);
		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(c_set);
		List<Formula> formula_list = pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter(onto))));
		
		Forgetter ft = new Forgetter();
		List<Formula> forgetting_solution = ft.Forgetting(r_sig, c_sig, formula_list);
		
		BackConverter bc = new BackConverter();
		OWLOntology view = bc.toOWLOntology(forgetting_solution);
				
		return view;
	}
		
	public List<Formula> FameRC(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig, List<Formula> formula_list) throws Exception {

		if (r_sig.isEmpty() && c_sig.isEmpty()) {
			return formula_list;
		}
				
		Forgetter ft = new Forgetter(); 

		List<Formula> forgetting_solution = ft.Forgetting(r_sig, c_sig, formula_list);
		
	
		return forgetting_solution;
	}
	


	
}