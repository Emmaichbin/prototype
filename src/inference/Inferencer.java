package inference;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

//import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
//import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
//import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.TopConcept;
import roles.AtomicRole;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import formula.Formula;

public class Inferencer {
	
	//private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	//private OWLDataFactory factory = manager.getOWLDataFactory();
	
	//LoadButtonListener lbl = new LoadButtonListener();
	
	//OWLOntology onto = lbl.ontology;

	
	public Inferencer() {

	}
	
	public List<Formula> combination_A(AtomicConcept concept, List<Formula> formula_list, OWLOntology onto)
			throws Exception {
		
		//System.out.println("onto = " + onto);
		
		//System.out.println("combine formula_list = " + formula_list);
		List<Formula> output_list = new ArrayList<>();
				
		// C or A
		List<Formula> positive_star_premises = new ArrayList<>();
		// C or exists r.A
		List<Formula> positive_exists_premises = new ArrayList<>();
		// C or exists r.(A or B)
		List<Formula> negative_star_premises = new ArrayList<>();
		// C or exists r.~A
		List<Formula> negative_star_and_premises = new ArrayList<>();
		// C or exists r.~A
		List<Formula> negative_exists_premises = new ArrayList<>();
		// C or exists r.(~A or B)

		EChecker ec = new EChecker();

		for (Formula formula : formula_list) {
			//If concept is not present in formula, then formula is directly put into the output_list. 
			
			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);
			//System.out.println("formula = " + formula);
			
			if (!ec.isPresent(concept, formula)) {
				output_list.add(formula);

			} else if (subsumer.equals(concept)) {
				positive_star_premises.add(formula);
	
			} else if (subsumer instanceof Exists && ec.isPresent(concept, subsumer)) {
				positive_exists_premises.add(formula);
	
			} else if (subsumee.equals(concept)) {
				negative_star_premises.add(formula);

			} else if (subsumee instanceof And) {
				if (subsumee.getSubFormulas().contains(concept)) {
					negative_star_and_premises.add(formula);
				} else {
					negative_exists_premises.add(formula);
				}
				
			} else if (subsumee instanceof Exists) {
				negative_exists_premises.add(formula);

			} else {
				throw new Exception("Damn! Error!");
			}
		}
		//System.out.println("=====================================================");
		//System.out.println("positive_star_premises = " + positive_star_premises);
		//System.out.println("positive_exists_premises = " + positive_exists_premises);
		//System.out.println("positive_exists_disjunction_premises = " + positive_exists_disjunction_premises);
		//System.out.println("positive_forall_premises = " + positive_forall_premises.size());
		//System.out.println("positive_forall_disjunction_premises = " + positive_forall_disjunction_premises);
		//System.out.println("negative_star_premises = " + negative_star_premises);
		//System.out.println("negative_exists_premises = " + negative_exists_premises);
		//System.out.println("negative_exists_disjunction_premises = " + negative_exists_disjunction_premises);
		//System.out.println("negative_forall_premises = " + negative_forall_premises.size());
		//System.out.println("negative_forall_disjunction_premises = " + negative_forall_disjunction_premises);
		//
		//Case I
		if (!positive_star_premises.isEmpty()) {
			for (Formula ps_premise : positive_star_premises) {
				Formula subsumee = ps_premise.getSubFormulas().get(0);
				//System.out.println("subsumee = " + subsumee);
				if (!negative_star_premises.isEmpty()) {
					for (Formula ns_premise : negative_star_premises) {
						output_list.add(AckermannReplace(concept, ns_premise, subsumee));
					}
				}
				if (!negative_star_and_premises.isEmpty()) {
					for (Formula nsa_premise : negative_star_and_premises) {
						output_list.add(AckermannReplace(concept, nsa_premise, subsumee));
					}
				}
				if (!negative_exists_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(AckermannReplace(concept, ne_premise, subsumee));
					}
				}
			}
		}

		// Case II
		if (!positive_exists_premises.isEmpty()) {
			// OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto);

			if (negative_star_premises.isEmpty() && negative_star_and_premises.isEmpty()
					&& negative_exists_premises.isEmpty()) {

				for (Formula pe_premise : positive_exists_premises) {
					output_list.add(AckermannReplace(concept, pe_premise, TopConcept.getInstance()));
				}

			} else {

				for (Formula pe_premise : positive_exists_premises) {

					if (!negative_star_premises.isEmpty()) {
						for (Formula ns_premise : negative_star_premises) {
							Formula subsumee = ns_premise.getSubFormulas().get(1);
							output_list.add(AckermannReplace(concept, pe_premise, subsumee));
						}
					}
				}
			}
		}
		
		
		//System.out.println("The output list of Ackermann_A: " + output_list);
		return output_list;
	}
	
	public List<Formula> combination_R(AtomicRole role, List<Formula> formula_list, OWLOntology onto)
			throws Exception {
		
		//System.out.println("onto = " + onto);
		
		//System.out.println("combine formula_list = " + formula_list);
		List<Formula> output_list = new ArrayList<>();
				
		// C or A
		List<Formula> positive_star_premises = new ArrayList<>();
		// C or exists r.A
		List<Formula> positive_exists_premises = new ArrayList<>();
		// C or exists r.(A or B)
		List<Formula> negative_star_premises = new ArrayList<>();
		// C or exists r.~A
		List<Formula> negative_exists_premises = new ArrayList<>();
		// C or exists r.(~A or B)

		EChecker ec = new EChecker();
		BackConverter bc = new BackConverter();
		OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto);
		//OWLReasonerFactory reasonerFactory = new ElkReasonerFactory();
		//OWLReasoner reasoner = reasonerFactory.createReasoner(onto);
		//reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);

		for (Formula formula : formula_list) {
			
			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);
			
			if (!ec.isPresent(role, formula)) {
				output_list.add(formula);

			} else if (subsumer.equals(role)) {
				positive_star_premises.add(formula);
	
			} else if (subsumee.equals(role)) {
				negative_star_premises.add(formula);

			} else if (ec.isPresent(role, subsumer)) {
				positive_exists_premises.add(formula);
	
			} else {
				negative_exists_premises.add(formula);
			}
		}
		//System.out.println("=====================================================");
		/*System.out.println("positive_star_premises = " + positive_star_premises);
		System.out.println("positive_exists_premises = " + positive_exists_premises);
		System.out.println("positive_exists_disjunction_premises = " + positive_exists_disjunction_premises);
		System.out.println("positive_forall_premises = " + positive_forall_premises.size());
		System.out.println("positive_forall_disjunction_premises = " + positive_forall_disjunction_premises);
		System.out.println("negative_star_premises = " + negative_star_premises);
		System.out.println("negative_exists_premises = " + negative_exists_premises);
		System.out.println("negative_exists_disjunction_premises = " + negative_exists_disjunction_premises);
		System.out.println("negative_forall_premises = " + negative_forall_premises.size());
		System.out.println("negative_forall_disjunction_premises = " + negative_forall_disjunction_premises);*/
		//
		//Case I
		
		for (Formula ps_premise : positive_star_premises) {
			Formula subsumee = ps_premise.getSubFormulas().get(0);
			for (Formula ns_premise : negative_star_premises) {
				output_list.add(AckermannReplace(role, ns_premise, subsumee));
			}	
			for (Formula ne_premise : negative_exists_premises) {
				output_list.add(AckermannReplace(role, ne_premise, subsumee));
			}	
		}	

		// Case II
		for (Formula ns_premise : negative_star_premises) {
			Formula subsumer = ns_premise.getSubFormulas().get(1);
			for (Formula pe_premise : positive_exists_premises) {
				output_list.add(AckermannReplace(role, pe_premise, subsumer));
			}
		}
		
		// Case III
		for (Formula pe_premise : positive_exists_premises) {
			//System.out.println("test = " + pe_premise);
			Formula pe_subsumee = pe_premise.getSubFormulas().get(0);
			Formula pe_subsumer = pe_premise.getSubFormulas().get(1);
			Formula pe_subsumer_filler = pe_subsumer.getSubFormulas().get(1);
			for (Formula ne_premise : negative_exists_premises) {
				Formula ne_subsumee = ne_premise.getSubFormulas().get(0);
				Formula ne_subsumer = ne_premise.getSubFormulas().get(1);
				Formula ne_subsumee_filler = null;
				Formula stored_conjunct = null;
				if (ne_subsumee instanceof Exists) {
					ne_subsumee_filler = ne_subsumee.getSubFormulas().get(1);
				} else {
					Set<Formula> conjunct_set = ne_subsumee.getSubformulae();
					for (Formula conjunct : conjunct_set) {
						if (ec.isPresent(role, conjunct)) {
							ne_subsumee_filler = conjunct.getSubFormulas().get(1);
							stored_conjunct = conjunct;
							break;
						}
					}
				}
				//OWLClassExpression owl_pe_subsumer_filler = bc.toOWLClassExpression(pe_subsumer_filler);
				//OWLClassExpression owl_ne_subsumee_filler = bc.toOWLClassExpression(ne_subsumee_filler);
				Formula inclusion = new Inclusion(pe_subsumer_filler, ne_subsumee_filler);
				OWLAxiom axiom = bc.toOWLSubClassOfAxiom(inclusion);
				if (reasoner.isEntailed(axiom)) {
					Formula new_inclusion = null;
					if (ne_subsumee instanceof Exists) {
						new_inclusion = new Inclusion(pe_subsumee, ne_subsumer);
					} else {
						Set<Formula> new_conjunct_set = new HashSet<>(ne_subsumee.getSubformulae());
						new_conjunct_set.remove(stored_conjunct);
						new_conjunct_set.add(pe_subsumee);
						Formula new_subsumee = new And(new_conjunct_set);
						new_inclusion = new Inclusion(new_subsumee, ne_subsumer);
					} 
					//System.out.println("Looking forward = " + new_inclusion);
					output_list.add(new_inclusion);
				}
			}	
		}
		
		//System.out.println("The output list of Ackermann_A: " + output_list);
		return output_list;
	}
	

	public List<Formula> Purify(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(Purify(concept, formula));
			}
		}

		return output_list;
	}

	public Formula AckermannReplace(AtomicRole role, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return new AtomicConcept(toBeReplaced.getText());

		} else if (toBeReplaced instanceof AtomicRole) {
			return toBeReplaced.equals(role) ? definition : new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Inclusion) {
			return new Inclusion(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			Set<Formula> conjunct_list = toBeReplaced.getSubformulae();
			Set<Formula> conjunct_set = new HashSet<>();
			for (Formula conjunct : conjunct_list) {
				conjunct_set.add(AckermannReplace(role, conjunct, definition));
			}
			return new And(conjunct_set);

		}

		return toBeReplaced;
	}
	
	public Formula AckermannReplace(AtomicConcept concept, Formula toBeReplaced, Formula definition) {
		
		//System.out.println(concept);
		//System.out.println(toBeReplaced);
		//System.out.println(definition);
		

		if (toBeReplaced instanceof AtomicConcept) {
			return toBeReplaced.equals(concept) ? definition : new AtomicConcept(toBeReplaced.getText());
			
		} else if (toBeReplaced instanceof AtomicRole) {
			return new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Inclusion) {
			return new Inclusion(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			Set<Formula> conjunct_list = toBeReplaced.getSubformulae();
			Set<Formula> conjunct_set = new HashSet<>();
			for (Formula conjunct : conjunct_list) {
				conjunct_set.add(AckermannReplace(concept, conjunct, definition));
			}
			return new And(conjunct_set);
			
		} 
		
		return toBeReplaced;
	}
	
	public static void main(String[] args) {	
		AtomicConcept a = new AtomicConcept("A");
		AtomicConcept b = new AtomicConcept("B");
		AtomicConcept c = new AtomicConcept("C");
		AtomicRole r = new AtomicRole("r");
		Exists e = new Exists(r, b);
		Set<Formula> list = new HashSet<>();
		list.add(a);
		list.add(c);
		And and = new And(list);
		Inclusion inc = new Inclusion(e, and);
		FChecker fc = new FChecker();
		System.out.println("e.c_sig = " + fc.negative(b, inc));
		Inferencer inf = new Inferencer();
		System.out.println("e.c_sig = " + inf.Purify(b, inc));
		
	}
	
	public Formula Purify(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? TopConcept.getInstance() : new AtomicConcept(formula.getText());
			
		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Exists) {
			return new Exists(Purify(concept, formula.getSubFormulas().get(0)),
					Purify(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Inclusion) {
			return new Inclusion(Purify(concept, formula.getSubFormulas().get(0)),
					Purify(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof And) {
			Set<Formula> conjunct_list = formula.getSubformulae();
			Set<Formula> conjunct_set = new HashSet<>();
			for (Formula conjunct : conjunct_list) {
				conjunct_set.add(Purify(concept, conjunct));
			}
			return new And(conjunct_set);
			
		}

		return formula;
	}
	
}
