package forgetting;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import checkfrequency.FChecker;
import checkreducedform.RFChecker;
import concepts.AtomicConcept;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import roles.AtomicRole;

public class Forgetter {

	public List<Formula> Forgetting(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig,
			List<Formula> formula_list_normalised) throws Exception {

		System.out.println("The Forgetting Starts:");

		DefinerIntroducer di = new DefinerIntroducer();
		//Simplifier pp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		
		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int i = 1;
			for (AtomicRole role : r_sig) {
				System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				pivot_list_normalised = se.getRoleSubset(role, r_sig_list_normalised);
				if (pivot_list_normalised.isEmpty()) {

				} else {
					pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);
					pivot_list_normalised = inf.combination_R(role, pivot_list_normalised);
					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(r_sig_list_normalised);
		}
		
		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			for (AtomicConcept concept : c_sig) {
				System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);

				if (pivot_list_normalised.isEmpty()) {
					
				} else {
					pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);	
					pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised);
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(c_sig_list_normalised);
		}
		
		
		if (!di.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;
				
			int k = 1;
			do {
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful (D1)!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);
					return formula_list_normalised;
				}

				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
			

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised);
						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);
					}
				}

			} while (definer_set.size() > di.definer_set.size());
			////this is the case of the cyclic cases, that's why the ACK_A is not re-used. 
			//In case the results of contains this case. report!
			do {
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful (D2)!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);
					return formula_list_normalised;
				}
				
				System.out.println("The formula might contain cylic case: " + d_sig_list_normalised);
				
				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(inf.PurifyPositive(concept, pivot_list_normalised));
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(inf.PurifyNegative(concept, pivot_list_normalised));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(inf.AckermannPositive(concept, pivot_list_normalised));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(inf.AckermannNegative(concept, pivot_list_normalised));
						di.definer_set.remove(concept);

					} else {
						d_sig_list_normalised.addAll(pivot_list_normalised);
					}
				}

			} while (definer_set.size() > di.definer_set.size());

		}
		
		System.out.println("Forgetting Successful!");
		
		return formula_list_normalised;
	}

}
