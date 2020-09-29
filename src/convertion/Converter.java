/*
1 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package convertion;

import concepts.AtomicConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;
import roles.RoleExpression;
import roles.TopRole;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;



/**
 *
 * @author Yizheng
 */
public class Converter {
		
	public AtomicConcept getConceptfromClass(OWLEntity owlClass) {
		return new AtomicConcept(owlClass.getIRI().toString());
	}
	
	public AtomicRole getRoleFromObjectProperty(OWLEntity owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().toString());
	}
	
	public Set<AtomicConcept> getConceptsfromClasses(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_set;
	}
				
	public List<AtomicConcept> getConceptsInSignature(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			concept_list.add(getConceptfromClass(owlClass));
		}

		return concept_list;
	}
		
	public List<AtomicRole> getRolesInSignature(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_list.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_list;
	}

	public List<Formula> OntologyConverter(OWLOntology ontology) {

		List<Formula> axiom_list = new ArrayList<>();		
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			axiom_list.addAll(AxiomConverter(owlAxiom));
		}

		return axiom_list;
	}
	
	
	public List<Formula> AxiomsConverter(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
		
	public List<Formula> AxiomConverter(OWLAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula converted = new Inclusion(ClassExpressionConverter(owlSCOA.getSubClass()),
					ClassExpressionConverter(owlSCOA.getSuperClass()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Collection<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula converted = new Inclusion(RoleExpressionConverter(owlSOPOA.getSubProperty()),
					RoleExpressionConverter(owlSOPOA.getSuperProperty()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Collection<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter(owlSOPOA));
			}
			return converted;
			
		} 

		return Collections.emptyList();
	}


	private Formula ClassExpressionConverter(OWLClassExpression concept) {
	
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().toString());

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Exists(RoleExpressionConverter(owlOSVF.getProperty()),
					ClassExpressionConverter(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter(conjunct));
			}
			return new And(conjunct_list);

		} 

		return TopConcept.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter(OWLObjectPropertyExpression role) {

		if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().toString());
			
		}
		
		return TopRole.getInstance();
	}
	
	public OWLOntology toOWLSubClassOfAxiom(OWLOntology onto) throws OWLOntologyCreationException {

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology onto_prime = manager.createOntology(IRI.generateDocumentIRI());
		for (OWLLogicalAxiom axiom : onto.getLogicalAxioms()) {
			manager.addAxioms(onto_prime, toOWLSubClassOfAxiom(axiom));
		}

		return onto_prime;
	}
	
	public Set<OWLSubClassOfAxiom> toOWLSubClassOfAxiom(OWLLogicalAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			return Collections.singleton(owlSCOA);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			return owlECA.asOWLSubClassOfAxioms();

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			return Collections.singleton(owlOPDA.asOWLSubClassOfAxiom());

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			return Collections.singleton(owlOPRA.asOWLSubClassOfAxiom());

		} 

		return Collections.emptySet();
	}

}
