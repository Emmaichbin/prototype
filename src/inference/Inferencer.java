package inference;

import java.util.ArrayList;
import java.util.List;



import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import roles.AtomicRole;
import roles.BottomRole;
import roles.TopRole;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;

public class Inferencer {
	
	//private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	//private OWLDataFactory factory = manager.getOWLDataFactory();
	
	//LoadButtonListener lbl = new LoadButtonListener();
	
	//OWLOntology onto = lbl.ontology;

	
	public Inferencer() {

	}
	
	public List<Formula> combination_A(AtomicConcept concept, List<Formula> formula_list)
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
			System.out.println("formula = " + formula);
			
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
		if (!positive_star_premises.isEmpty()) {
			for (Formula ps_premise : positive_star_premises) {
				Formula subsumee = ps_premise.getSubFormulas().get(0);
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
	
	public List<Formula> combination_R(AtomicRole role, List<Formula> formula_list)
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

		for (Formula formula : formula_list) {
			//If concept is not present in formula, then formula is directly put into the output_list. 
			
			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);
			
			if (!ec.isPresent(role, formula)) {
				output_list.add(formula);

			} else if (subsumer.equals(role)) {
				positive_star_premises.add(formula);
	
			} else if (subsumer instanceof Exists && ec.isPresent(role, subsumer)) {
				positive_exists_premises.add(formula);
	
			} else if (subsumee.equals(role)) {
				negative_star_premises.add(formula);

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
		if (!positive_star_premises.isEmpty()) {
			if (!negative_star_premises.isEmpty()) {
				for (Formula ps_premise : positive_star_premises) {
					Formula subsumee = ps_premise.getSubFormulas().get(0);
					for (Formula ns_premise : negative_star_premises) {
						output_list.add(AckermannReplace(role, ns_premise, subsumee));
					}	
				}			
			}
			
			if (!negative_exists_premises.isEmpty()) {
				for (Formula ps_premise : positive_star_premises) {
					Formula subsumee = ps_premise.getSubFormulas().get(0);
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(AckermannReplace(role, ne_premise, subsumee));
					}	
				}	
			}
		}

		// Case II
		if (!positive_exists_premises.isEmpty()) {		
			if (!negative_star_premises.isEmpty()) {
				for (Formula ns_premise : negative_star_premises) {
					Formula subsumer = ns_premise.getSubFormulas().get(1);
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(AckermannReplace(role, pe_premise, subsumer));
					}
				}				
			}
		}
		
		//System.out.println("The output list of Ackermann_A: " + output_list);
		return output_list;
	}
		

	
	
	public List<Formula> AckermannPositive(AtomicConcept concept, List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(concept)) {
				definition = TopConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(concept);
				if (other_list.size() == 1) {
					disjunct_list.add(new Negation(other_list.get(0)));
					continue;
				} else {
					disjunct_list.add(new Negation(new Or(other_list)));
					continue;
				}
			}
		}

		if (definition != TopConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new Or(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}
	
	public List<Formula> AckermannNegative(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {
		
		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();

		for (Formula formula : input_list) {
			if (cf.negative(concept, formula) == 0) {
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(new Negation(concept))) {
				definition = BottomConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(new Negation(concept));
				if (other_list.size() == 1) {
					disjunct_list.add(other_list.get(0));
					continue;
				} else {
					disjunct_list.add(new Or(other_list));
					continue;
				}
			}
		}

		if (definition != BottomConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new And(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(concept, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.negative(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyNegative(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicConcept concept, List<Formula> inputList)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> outputList = new ArrayList<>();

		for (Formula formula : inputList) {
			if (cf.negative(concept, formula) == 0) {
				outputList.add(formula);
			} else {
				outputList.add(PurifyNegative(concept, formula));
			}
		}

		return outputList;
	}

	public Formula AckermannReplace(AtomicRole role, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return new AtomicConcept(toBeReplaced.getText());

		} else if (toBeReplaced instanceof AtomicRole) {
			return toBeReplaced.equals(role) ? definition : new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Individual) {
			return new Individual(toBeReplaced.getText());
		
		} else if (toBeReplaced instanceof Negation) {
			return new Negation(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition));

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Forall) {
			return new Forall(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(role, conjunct, definition));
			}
			return new And(new_conjunct_list);

		} else if (toBeReplaced instanceof Or) {
			List<Formula> disjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(AckermannReplace(role, disjunct, definition));
			}
			return new Or(new_disjunct_list);

		}

		return toBeReplaced;
	}
	
	public Formula AckermannReplace(AtomicConcept concept, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return toBeReplaced.equals(concept) ? definition : new AtomicConcept(toBeReplaced.getText());
			
		} else if (toBeReplaced instanceof AtomicRole) {
			return new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(concept, conjunct, definition));
			}
			return new And(new_conjunct_list);
			
		} 
		
		return toBeReplaced;
	}
	
	public Formula PurifyPositive(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? TopRole.getInstance() : new AtomicRole(formula.getText());
		
		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyNegative(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? BottomRole.getInstance() : new AtomicRole(formula.getText());
		
		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyPositive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? TopConcept.getInstance() : new AtomicConcept(formula.getText());
			
		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(concept, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
			
	public Formula PurifyNegative(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? BottomConcept.getInstance() : new AtomicConcept(formula.getText());

		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(concept, conjunct));
			}
			return new And(new_conjunct_list);

		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
}
