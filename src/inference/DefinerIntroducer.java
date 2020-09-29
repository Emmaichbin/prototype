package inference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLEntity;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;

public class DefinerIntroducer {

	public DefinerIntroducer() {

	}

	public static Map<Formula, AtomicConcept> definer_left_map = new HashMap<>();
	public static Map<Formula, AtomicConcept> definer_right_map = new HashMap<>();
	public static Set<OWLEntity> owldefiner_set = new HashSet<>();
	public Set<AtomicConcept> definer_set = new HashSet<>();

	public List<Formula> distribute(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(distribute(formula));
		}

		return output_list;
	}

	public List<Formula> distribute(Formula formula) {

		List<Formula> output_list = new ArrayList<>();

		if (formula instanceof Inclusion) {
			Formula subsumer = formula.getSubFormulas().get(1);
			if (subsumer instanceof And) {
				Formula subsumee = formula.getSubFormulas().get(0);
				List<Formula> conjunct_list = subsumer.getSubFormulas();
				for (Formula conjunct : conjunct_list) {
					if (!subsumee.equals(conjunct)) {
						output_list.add(new Inclusion(subsumee, conjunct));
					}
				}
			}
		}

		return output_list;
	}

	public List<Formula> introduceDefiners(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(concept, formula));
		}

		return output_list;
	}

	private List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) {

		System.out.println("formula = " + formula);

		List<Formula> output_list = new ArrayList<>();
		FChecker fc = new FChecker();

		Formula subsumee = formula.getSubFormulas().get(0);
		Formula subsumer = formula.getSubFormulas().get(1);

		int A_subsumee = fc.positive(concept, subsumee);
		int A_subsumer = fc.positive(concept, subsumer);
		
		if (subsumee.equals(subsumer)) {
			
		} else if (A_subsumee == 0 && A_subsumer == 0) {
			output_list.add(formula);

		} else if (A_subsumee == 1 && A_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And && !filler.getSubFormulas().contains(concept)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						List<Formula> filler_conjunct_list = filler.getSubFormulas();
						for (Formula filler_conjunct : filler_conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_conjunct, definer)));
						}

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(concept, conjunct) != 0 && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);
						// B and exists r.exists s.A in C
						if (filler instanceof Exists) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
							// B and exists r.(C and exists s.A)
						} else if (filler instanceof And && !filler.getSubFormulas().contains(concept)) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								List<Formula> filler_conjunct_list = filler.getSubFormulas();
								for (Formula filler_conjunct : filler_conjunct_list) {
									output_list.addAll(
											introduceDefiners(concept, new Inclusion(filler_conjunct, definer)));
								}
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}

						} else {
							output_list.add(formula);
							break;
						}

					} else if (conjunct.equals(concept)) {
						output_list.add(formula);
						break;
					}
				}

			} else {
				output_list.add(formula);
			}

		} else if (A_subsumee > 1 && A_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						List<Formula> filler_conjunct_list = filler.getSubFormulas();
						for (Formula filler_conjunct : filler_conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_conjunct, definer)));
						}

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(concept, conjunct) != 0 && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (filler instanceof And) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								List<Formula> filler_conjunct_list = filler.getSubFormulas();
								for (Formula filler_conjunct : filler_conjunct_list) {
									output_list.addAll(
											introduceDefiners(concept, new Inclusion(filler_conjunct, definer)));
								}
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}

						} else {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}
						}
					}
				}
			}

		} else if (A_subsumee == 0 && A_subsumer == 1) {

			System.out.println("A_subsumee == 0 && A_subsumer == 1");

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, filler)));

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And && !filler.getSubFormulas().contains(concept)) {
					
					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						List<Formula> conjunct_list = filler.getSubFormulas();
						for (Formula conjunct : conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, conjunct)));
						}

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else {
				output_list.add(formula);
			}

		} else if (A_subsumee == 1 && A_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula filler_1 = subsumee.getSubFormulas().get(1);
				
				if (filler_1 instanceof Exists) {

					if (definer_right_map.get(filler_1) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler_1, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler_1);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}

				} else if (filler_1 instanceof And && !filler_1.getSubFormulas().contains(concept)) {

					if (definer_right_map.get(filler_1) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler_1, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						List<Formula> filler_1_conjunct_list = filler_1.getSubFormulas();
						for (Formula filler_1_conjunct : filler_1_conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1_conjunct, definer)));
						}

					} else {
						AtomicConcept definer = definer_right_map.get(filler_1);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {					

					if (fc.positive(concept, conjunct) != 0 && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (filler instanceof Exists) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else if (filler instanceof And && !filler.getSubFormulas().contains(concept)) {
							
							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								List<Formula> filler_1_conjunct_list = filler.getSubFormulas();
								for (Formula filler_1_conjunct : filler_1_conjunct_list) {
									output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1_conjunct, definer)));
								}
								break;
								
							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}			
							
						} else {
							
							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
							
						}

					} else if (conjunct.equals(concept)) {

						if (definer_left_map.get(subsumer) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_left_map.put(subsumer, definer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
							break;

						} else {
							AtomicConcept definer = definer_left_map.get(subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							break;
						}
					}
				}

			} else {
				
				if (definer_left_map.get(subsumer) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(subsumer, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

				} else {
					AtomicConcept definer = definer_left_map.get(subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}
				
			}

		} else if (A_subsumee > 1 && A_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
					output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(concept, conjunct) != 0) {

						Formula filler_2 = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler_2) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler_2, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_2, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler_2);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							break;
						}
					}
				}
			}

		} else if (A_subsumee == 0 && A_subsumer > 1) {

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, filler)));

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						List<Formula> conjunct_list = filler.getSubFormulas();
						for (Formula conjunct : conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, conjunct)));
						}

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}
			}

		} else if (A_subsumee == 1 && A_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler_1 = subsumee.getSubFormulas().get(1);

				if (filler_1 instanceof Exists) {

					if (definer_right_map.get(filler_1) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler_1, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler_1);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}

				} else if (filler_1 instanceof And && !filler_1.getSubFormulas().contains(concept)) {
					
					if (definer_right_map.get(filler_1) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler_1, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						List<Formula> filler_1_conjunct_list = filler_1.getSubFormulas();
						for (Formula filler_1_conjunct : filler_1_conjunct_list) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1_conjunct, definer)));
						}

					} else {
						AtomicConcept definer = definer_right_map.get(filler_1);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}				
					
				} else {
					
					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(concept, conjunct) != 0 && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (filler instanceof Exists) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else if (filler instanceof And && !filler.getSubFormulas().contains(concept)) {
							
							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								List<Formula> filler_1_conjunct_list = filler.getSubFormulas();
								for (Formula filler_1_conjunct : filler_1_conjunct_list) {
									output_list.addAll(introduceDefiners(concept, new Inclusion(filler_1_conjunct, definer)));
								}
								break;
								
							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}			
							
						} else {

							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}

					} else if (conjunct.equals(concept)) {
						
						if (definer_left_map.get(subsumer) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_left_map.put(subsumer, definer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
							break;

						} else {
							AtomicConcept definer = definer_left_map.get(subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							break;
						}
					}
				}
				
			} else {
				
				if (definer_left_map.get(subsumer) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(subsumer, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

				} else {
					AtomicConcept definer = definer_left_map.get(subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}
				
			}

		} else if (A_subsumee > 1 && A_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
					output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(concept, conjunct) != 0 && conjunct instanceof Exists) {

						Formula filler_2 = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler_2) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler_2, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler_2, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler_2);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							break;
						}
					}
				}
			}

		} else {
			output_list.add(formula);
		}

		return output_list;
	}

	public List<Formula> introduceDefiners(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(role, formula));
		}

		return output_list;
	}

	private List<Formula> introduceDefiners(AtomicRole role, Formula formula) {

		List<Formula> output_list = new ArrayList<>();
		FChecker fc = new FChecker();

		Formula subsumee = formula.getSubFormulas().get(0);
		Formula subsumer = formula.getSubFormulas().get(1);

		int r_subsumee = fc.positive(role, subsumee);
		int r_subsumer = fc.positive(role, subsumer);

		
		if (subsumee.equals(subsumer)) {
			
		} else if (r_subsumee == 0 && r_subsumer == 0) {
			output_list.add(formula);

		} else if (r_subsumee == 1 && r_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(role, conjunct) == 1) {

						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
							
						} else {
							output_list.add(formula);
							break;
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee > 1 && r_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (int i = 0; i < conjunct_list.size(); i++) {

					Formula conjunct = conjunct_list.get(i);
					int r_conjunct = fc.positive(role, conjunct);

					if (r_conjunct != 0 && r_subsumee == r_conjunct) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.add(formula);
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.add(formula);
							break;
						}

					} else if (r_conjunct != 0 && r_subsumee > r_conjunct) {

						if (definer_right_map.get(conjunct) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(conjunct, definer);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(conjunct);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}
					}
				}
			}

		} else if (r_subsumee == 0 && r_subsumer == 1) {

			if (subsumer instanceof Exists) {

				Formula relation = subsumer.getSubFormulas().get(0);
				Formula filler = subsumer.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, filler)));

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee == 1 && r_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(role, conjunct) == 1) {

						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {
							
							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								subsumer.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}	
						}
					} 
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee > 1 && r_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (int i = 0; i < conjunct_list.size(); i++) {

					Formula conjunct = conjunct_list.get(i);
					int r_conjunct = fc.positive(role, conjunct);

					if (r_conjunct != 0 && r_subsumee == r_conjunct) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}

					} else if (r_conjunct != 0 && r_subsumee > r_conjunct) {

						if (definer_right_map.get(conjunct) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(conjunct, definer);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(conjunct);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}
					}
				}
			}

		} else if (r_subsumee == 0 && r_subsumer > 1) {

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (definer_left_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(filler, definer);
					subsumer.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(role, new Inclusion(definer, filler)));

				} else {
					AtomicConcept definer = definer_left_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}
			}

		} else if (r_subsumee == 1 && r_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (Formula conjunct : conjunct_list) {

					if (fc.positive(role, conjunct) == 1) {

						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {
							
							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}					
						}
					} 
				}
			}

		} else if (r_subsumee > 1 && r_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
				}

			} else if (subsumee instanceof And) {

				List<Formula> conjunct_list = subsumee.getSubFormulas();

				for (int i = 0; i < conjunct_list.size(); i++) {

					Formula conjunct = conjunct_list.get(i);
					int r_conjunct = fc.positive(role, conjunct);

					if (r_conjunct != 0 && r_subsumee == r_conjunct) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}

					} else if (r_conjunct != 0 && r_subsumee > r_conjunct) {

						if (definer_right_map.get(conjunct) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(conjunct, definer);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(conjunct);
							conjunct_list.set(i, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}
					}
				}
			}

		} else {
			output_list.add(formula);
		}

		System.out.println("after definer = " + output_list);
		return output_list;
	}

}
