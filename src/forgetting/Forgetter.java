package forgetting;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLOntology;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import roles.AtomicRole;

public class Forgetter {

	public List<Formula> Forgetting(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig,
			List<Formula> formula_list_normalised, OWLOntology onto) throws Exception {

		System.out.println("The Forgetting Starts:");

		DefinerIntroducer di = new DefinerIntroducer();
		//Simplifier pp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();

		
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
					pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto);
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
					
				} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
						fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));

				} else {
					pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);	
					pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(c_sig_list_normalised);
		}
		
		
		if (!DefinerIntroducer.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(DefinerIntroducer.definer_set, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;
			////this is the case of the cyclic cases, that's why the ACK_A is not re-used. 
			//In case the results of contains this case. report!
			int k = 1;
			do {
				if (DefinerIntroducer.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);
					return formula_list_normalised;
				}
				
				definer_set = new HashSet<>(DefinerIntroducer.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
							fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));
						DefinerIntroducer.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
						d_sig_list_normalised.addAll(pivot_list_normalised);
						DefinerIntroducer.definer_set.remove(concept);
					}
				}

			} while (true);

		}
		
		//System.out.println("DefinerIntroducer.definer_set = " + DefinerIntroducer.definer_set);
		
		return formula_list_normalised;
	}
	
	/*
	 * else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(inf.AckermannPositive(concept, pivot_list_normalised));
						DefinerIntroducer.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(inf.AckermannNegative(concept, pivot_list_normalised));
						DefinerIntroducer.definer_set.remove(concept);

					} 
	 */

}
