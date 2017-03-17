package gov.nih.nci.owl;

/*
 * Robert Wynne, MSC
 * Tracy Safran, Leidos
 *
 * Center for Bioinformatics and Information Technology (CBIIT)
 * Enterprise Vocabulary Services (EVS)
 *
 * Last Modified: 8/18 for Cancer Moonshot Phase 1
 *                In Support of OCPL Clinical Trials Search API
 */

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;
import java.util.Vector;

import org.coode.owl.rdf.rdfxml.RDFXMLOntologyStorer;
import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.inference.OWLClassReasoner;
import org.semanticweb.owl.io.OWLXMLOntologyFormat;
import org.semanticweb.owl.io.WriterOutputTarget;
import org.semanticweb.owl.model.AddAxiom;
import org.semanticweb.owl.model.OWLAnnotation;
import org.semanticweb.owl.model.OWLAnnotationAxiom;
import org.semanticweb.owl.model.OWLAxiom;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.model.OWLDataFactory;
import org.semanticweb.owl.model.OWLDataProperty;
import org.semanticweb.owl.model.OWLDataType;
import org.semanticweb.owl.model.OWLDescription;
import org.semanticweb.owl.model.OWLEntity;
import org.semanticweb.owl.model.OWLEntityAnnotationAxiom;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLIndividual;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLOntologyChange;
import org.semanticweb.owl.model.OWLOntologyManager;
import org.semanticweb.owl.model.OWLTypedConstant;
import org.semanticweb.owl.model.RemoveAxiom;
import org.semanticweb.owl.util.OWLEntityRemover;
import org.semanticweb.owl.util.ToldClassHierarchyReasoner;

// TODO: Auto-generated Javadoc
/**
 * The Class OWLScrubber.
 */
public class OWLScrubber {

	/**
	 * The main method. Creates OWLScrubber, configures it, then runs it
	 * 
	 * @param args
	 *            the arguments
	 */
	public static void main(String[] args) {
		try {
			OWLScrubber scrubber = new OWLScrubber();
			scrubber.configure(args);
			scrubber.run();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/** The ontology namespace. */
	private String ontologyNamespace;

	/** The physical uri where the file to be processed is found. */
	private URI physicalURI;

	/** The save uri where the output file should be written. */
	private URI saveURI;

	/** The type constant string. */
	private final String typeConstantString = "http://www.w3.org/2001/XMLSchema#string";

	/** The type constant literal. */
	private final String typeConstantLiteral = "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";

	/** The manager. */
	private OWLOntologyManager manager;

	/** The ontology. */
	private OWLOntology ontology;

	/** The suppress individuals. Should OWL#Individual be suppressed */
	private boolean suppressIndividuals = true;

	/** The has literals. Does the ontology possess instances of XML:Literal */
	private boolean hasLiterals = false;

	/** The for meme. Is the output intended for import into MEME */
	private final boolean forMeme = false;

	/** The for ftp. Is the output intended for publishing to the FTP */
	private final boolean forFtp = false;

	/**
	 * The construct synonyms. Should simple synonyms be constructed from
	 * comples FULL_SYNs
	 */
	private final boolean constructSynonyms = false;

	/**
	 * The pretty print. Should the output skip processing and just be a
	 * prettier version of the input
	 */
	private boolean prettyPrint = false;

	/** The scrub empty. Should empty qualifiers be scrubbed from the output */
	private boolean scrubEmpty = false;

	/**
	 * The prefix. If hasLiterals=true, then a prefix for the literal's
	 * definition must be supplied
	 */
	private String prefix = new String("");

	private PrintWriter pw;

	private String configFile = "./config/owlscrubber.properties";

	Vector<String> complexPropsToSimplify;

	/** The for ftp. Is the output intended for publishing to the FTP */
	private boolean generateFlatFile = false;

	/** The uri where the Flat File should be printied */
	private URI flatFileURI;

	/** The removed classes. */
	Vector<String> removedClasses = new Vector<String>();

	/** The branches to delete. */
	Vector<String> branchesToDelete;

	/** The properties to delete. */
	Vector<String> propertiesToDelete;

	/** The complex data to delete. */
	Vector<String> complexDataToDelete;

	/**
	 * Configure the OWLScrubber
	 * 
	 * @param args
	 *            the args
	 * @throws OWLException
	 *             the OWL exception
	 */
	public void configure(String[] args) throws Exception {
		if (args.length > 0) {
			for (int i = 0; i < args.length; i++) {
				String option = args[i];
				if (option.equalsIgnoreCase("--help")) {
					printHelp();
				} else if (option.equalsIgnoreCase("-E")
						|| option.equalsIgnoreCase("--Empty")) {
					scrubEmpty = true;
				} else if (option.equalsIgnoreCase("-I")
						|| option.equalsIgnoreCase("--Individuals")) {
					suppressIndividuals = false;
				} else if (option.equalsIgnoreCase("-L")
						|| option.equalsIgnoreCase("--Literals")) {
					hasLiterals = true;
					prefix = args[++i] + ":";
				} else if (option.equalsIgnoreCase("-C")
						|| option.equalsIgnoreCase("--Config")) {
					configFile = args[++i];
				} else if (option.equalsIgnoreCase("-F")
						|| option.equalsIgnoreCase("-Flat")) {
					generateFlatFile = true;
					flatFileURI = new URI(args[++i]);
				} else if (option.equalsIgnoreCase("-P")
						|| option.equalsIgnoreCase("--Pretty")) {
					prettyPrint = true;
				} else if (option.equalsIgnoreCase("-N")
						|| option.equalsIgnoreCase("--iNput")) {
					physicalURI = new URI(args[++i]);
				} else if (option.equalsIgnoreCase("-O")
						|| option.equalsIgnoreCase("--Output")) {
					saveURI = new URI(args[++i]);
				} else {
					printHelp();
				}

			}
		} else {
			printHelp(); // This will exit the program
		}

		String branchDeleteFile = "";
		String propsDeleteFile = "";
		String complexDeleteFile = "";
		String complexSimplifyFile = "";
		try {
			Properties props = new Properties();
			props.load(new FileInputStream(configFile));
			ontologyNamespace = props.getProperty("namespace");
			if (saveURI == null) {
				saveURI = new URI(props.getProperty("saveURI"));
			}
			if (physicalURI == null) {
				physicalURI = new URI(props.getProperty("inputURI"));
			}
			branchDeleteFile = props.getProperty("branch_delete");
			propsDeleteFile = props.getProperty("props_delete");
			complexDeleteFile = props.getProperty("complex_delete");
			complexSimplifyFile = props.getProperty("complex_simplify");
		} catch (Exception e) {
			e.printStackTrace();
			System.out
					.println("Unable to find owlscrubber.properties file in this directory.  Aborting.");
			System.exit(1);
		}
		try {
			this.manager = OWLManager.createOWLOntologyManager();
			this.ontology = manager.loadOntologyFromPhysicalURI(physicalURI);
		} catch (OWLException e) {
			e.printStackTrace();
			System.exit(1);
		}
		branchesToDelete = readConfigFile(branchDeleteFile);
		propertiesToDelete = readConfigFile(propsDeleteFile);
		complexDataToDelete = readConfigFile(complexDeleteFile);
		complexPropsToSimplify = readConfigFile(complexSimplifyFile);

	}

	/**
	 * Configure the PrintWriter
	 * 
	 * @param fileLoc
	 */
	private boolean config_pw(URI fileLoc) {
		try {
			File file = new File(fileLoc);
			pw = new PrintWriter(file);
			return true;
		} catch (Exception e) {
			System.out.println("Error in PrintWriter");
			return false;
		}
	}

	/**
	 * Construct clean property from a complex property
	 * 
	 * @param cleanProperty
	 *            - the id of the clean property to be created
	 * @param complexProperty
	 *            - the id of the complex property to be processed
	 * @param complexTagName
	 *            - not currently used
	 */
	public void constructCleanProperty(String cleanProperty,
			String complexProperty, String complexTagName) {
		Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();
		for (OWLAxiom ax : ontology.getAxioms()) {
			if (ax.toString().contains("Annotation(" + complexProperty)) {
				OWLEntity ent = getReferencingClassEntity(ax);
				String termName = getTagValue(ax, complexProperty);
				if (termName != null) {
					OWLDataFactory factory = manager.getOWLDataFactory();
					OWLDataType odt = factory.getOWLDataType(URI
							.create(typeConstantString));
					OWLTypedConstant otc = factory.getOWLTypedConstant(
							termName, odt);
					OWLAnnotation anno = factory.getOWLConstantAnnotation(
							createURI(cleanProperty), otc);
					OWLEntityAnnotationAxiom ax1 = factory
							.getOWLEntityAnnotationAxiom(ent, anno);
					changes.add(new AddAxiom(ontology, ax1));
				}
			}
		}
		if (!changes.isEmpty()) {
			List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
					changes);
			try {
				manager.applyChanges(list);
			} catch (OWLException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * Creates an OWL uri from the ontology namespace and a class name
	 * 
	 * @param className
	 *            the class name
	 * @return the uRI
	 */
	public URI createURI(String className) {
		return URI.create(ontologyNamespace + "#" + className);
	}

	/**
	 * Fix references. If a class is removed, then also remove any roles
	 * pointing to it.
	 */
	@SuppressWarnings("unchecked")
	public void fixReferences() {
		try {
			Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();
			for (OWLClass cls : ontology.getReferencedClasses()) {
				for (OWLAnnotationAxiom axiom : cls
						.getAnnotationAxioms(ontology)) {
					// associations only
					if (axiom.toString().contains("^^anyURI")) {
						int beginning = axiom.toString().indexOf("\"");
						int end = axiom.toString().indexOf("\"^^anyURI");
						String value = axiom.toString().substring(
								beginning + 1, end);
						if ((removedClasses != null) && (value != null)
								&& removedClasses.contains(value)) {
							System.out
									.println("Removing association from class "
											+ axiom.getSubject() + " - ");
							System.out.println("\t"
									+ axiom.getAnnotation().getAnnotationURI()
											.getFragment() + " " + value);
							changes.add(new RemoveAxiom(ontology, axiom));
						}
					}
				}
			}
			List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
					changes);
			manager.applyChanges(list);
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Gets the descendants.
	 * 
	 * @param cls
	 *            the cls
	 * @return the descendants
	 */
	public Vector<OWLDescription> getDescendants(OWLClass cls) {
		Set<OWLDescription> ods = cls.getSubClasses(ontology);
		OWLDescription[] children = ods.toArray(new OWLDescription[ods.size()]);
		if (children.length == 0) return null;
		Vector<OWLDescription> vChildren = new Vector<OWLDescription>();
		for (OWLDescription child : children) {
			vChildren.add(child);
		}
		for (int i = 0; i < vChildren.size(); i++) {
			Vector<OWLDescription> w = getDescendants(vChildren.elementAt(i)
					.asOWLClass());
			if (w != null) {
				for (int j = 0; j < w.size(); j++) {
					if (w.elementAt(j) != null
							&& !vChildren.contains(w.elementAt(j))) {
						vChildren.add(w.elementAt(j));
					}
				}
			}
		}
		return vChildren;
	}

	/**
	 * Gets the referenced class entity for an axiom
	 * 
	 * @param ax
	 *            the axiom
	 * @return the referencing class entity
	 */
	public OWLEntity getReferencingClassEntity(OWLAxiom ax) {
		OWLEntity ent = null;
		// assume only one class referenced for each axiom
		for (OWLEntity e : ax.getReferencedEntities()) {
			if (hasLiterals && !e.toString().equals("XMLLiteral")) {
				ent = e;
				break;
			}
			if (!hasLiterals && !e.toString().equals("string")) {
				ent = e;
				break;
			}
		}
		return ent;
	}

	/**
	 * Gets the tag value.
	 * 
	 * @param ax
	 *            the axiom
	 * @param tagName
	 *            the tag name
	 * @return the tag value
	 */
	public String getTagValue(OWLAxiom ax, String tagName) {
		String tagValue = null;
		int beginning = ax.toString().indexOf("\"");
		int end;
		if (hasLiterals) {
			end = ax.toString().indexOf("\"^^XMLLiteral))");
		} else {
			end = ax.toString().indexOf("\"^^string))");
		}
		String orig = ax.toString().substring(beginning + 1, end);
		int pos1 = orig.indexOf("<" + prefix + tagName + ">");
		int pos2 = orig.indexOf("</" + prefix + tagName + ">");
		if (pos1 != -1 && pos2 != -1) {
			tagValue = orig.substring(pos1 + 2 + prefix.length()
					+ tagName.length(), pos2); // 2 is < and >
		}
		return tagValue;
	}

	/**
	 * Checks if an axiom is empty.
	 * 
	 * @param ax
	 *            the ax
	 * @return true, if is empty
	 */
	public boolean isEmpty(OWLAxiom ax) {
		boolean test = false;

		// EntityAnnotationAxiom(OBI_0000639 Annotation(IAO_0000111 ""^^string))
		// EntityAnnotationAxiom(OBI_0000481 Annotation(IAO_0000118 ""@en))
		// EntityAnnotationAxiom(OBI_0400008 Comment( ""@en))

		if (ax.toString().contains(" \"\"^^")
				|| ax.toString().contains(" \"\"@")) {
			// System.out.println(ax);
			test = true;
		}
		return test;
	}

	/**
	 * Prints the help.
	 */
	public void printHelp() {
		System.out.println("");
		// System.out.println("Usage: OWLScrubber [OPTIONS] ... [OWL] [OUTPUT FILE]");
		System.out.println("Usage: OWLScrubber [OPTIONS] ");
		System.out.println(" ");
		System.out
				.println("  -C [configFile]\tTells where to find owlscrubber.properties file");
		System.out.println("  -E, --Empty\t\tScrub empty properties");
		System.out.println("  -I, --Individuals\t\tOutput OWL Individuals");
		System.out
				.println("  -L, --Literals [prefix]\tInput OWL contains XML Literals");
		// System.out
		// .println("  -M, --Meme\t\t\tOutput MEME file for publication");
		System.out
				.println("   -F, --Flat\t\t\tURL to print flat file (optional)");
		System.out.println("  -P, --Pretty\t\t\tPretty print, scrub nothing");
		// System.out.println("  -S, --Synonyms\t\tConstruct synonyms");
		System.out.println("  -N, --iNput\t\t\tURL of input file");
		System.out.println("  -O, --Output\t\t\tURL of output file");
		System.out.println("");
		System.exit(1);
	}

	/**
	 * Read config file.
	 * 
	 * @param filename
	 *            the filename
	 * @return the vector< string>
	 */
	public Vector<String> readConfigFile(String filename) {
		Vector<String> v = new Vector<String>();
		FileReader configFile = null;
		BufferedReader buff = null;
		try {
			configFile = new FileReader(filename);
			buff = new BufferedReader(configFile);
			boolean eof = false;
			while (!eof) {
				String line = buff.readLine();
				if (line == null) {
					eof = true;
				} else {
					v.add(line);
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			// Closing the streams
			try {
				buff.close();
				configFile.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		if (!v.isEmpty())
			return v;
		else
			return null;
	}

	/**
	 * Removes the branch.
	 * 
	 * @param classURI
	 *            the class uri
	 */
	public void removeBranch(URI classURI) {
		try {
			OWLEntityRemover remover = new OWLEntityRemover(manager,
					Collections.singleton(ontology));
			for (OWLClass cls : ontology.getReferencedClasses()) {
				// System.out.println(cls.getURI().toString());
				if (cls.getURI().equals(classURI)) {
					// System.out.println("Now printing all descendants of " +
					// cls);
					Vector<OWLDescription> descendants = getDescendants(cls);
					if (descendants != null) {
						for (OWLDescription odesc : descendants) {
							// System.out.println("Removing " + odesc );
							URI test = odesc.asOWLClass().getURI();
							removedClasses.add(test.toString());
							odesc.asOWLClass().accept(remover);
						}
					} else {
						// System.out.println("No children to remove from " +
						// cls + ".");
					}
					// System.out.println( "Removing branch class " + cls);
					cls.accept(remover);
				}
			}
			// System.out.println("Applying branch removal changes...");
			manager.applyChanges(remover.getChanges());
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Removes the complex property.
	 * 
	 * @param complex
	 *            the id of the complex property to be removed
	 */
	@SuppressWarnings("unchecked")
	public void removeComplex(String complex) {
		String[] complexArray = complex.split("\t");

		String[] values = new String[2];
		values[0] = null;
		values[1] = null;
		if (complex.contains("\t")) {
			values = complex.split("\t");
			if (values[0] != null && values[1] != null) {
				if (hasLiterals) {
					values[1] = prefix + values[1];
				}
				Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();
				for (OWLAxiom ax : ontology.getAxioms()) {
					if (ax.toString().contains("Annotation(" + values[0])
							&& ax.toString().contains(values[1])) {
						OWLEntity ent = getReferencingClassEntity(ax);
						// System.out.println(ax);

						// get property value, return the new value
						int beginning = ax.toString().indexOf("\"");
						int end;

						if (hasLiterals) {
							end = ax.toString().indexOf("\"^^XMLLiteral))");
						} else {
							end = ax.toString().indexOf("\"^^string))");
						}

						String origValue = ax.toString().substring(
								beginning + 1, end);
						String newValue = removeData(origValue, values[1]);
						// System.out.println( origValue );
						// System.out.println( "\t" + newValue );

						// delete old axiom
						changes.add(new RemoveAxiom(ontology, ax));

						// create new axiom
						OWLDataFactory factory = manager.getOWLDataFactory();
						OWLDataType odt;

						if (hasLiterals) {
							odt = factory.getOWLDataType(URI
									.create(typeConstantLiteral));
						} else {
							odt = factory.getOWLDataType(URI
									.create(typeConstantString));
						}

						OWLTypedConstant otc = factory.getOWLTypedConstant(
								newValue, odt);
						OWLAnnotation anno = factory.getOWLConstantAnnotation(
								createURI(values[0]), otc);
						OWLEntityAnnotationAxiom ax1 = factory
								.getOWLEntityAnnotationAxiom(ent, anno);
						changes.add(new AddAxiom(ontology, ax1));
						// System.out.println("New axiom looks like");
						// System.out.println(ax1);
					}
				}
				if (!changes.isEmpty()) {
					List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
							changes);
					try {
						// System.out.println("Applying changed complex properties...");
						manager.applyChanges(list);
					} catch (OWLException e) {
						e.printStackTrace();
					}
				}
			} else {
				System.err
						.println("Invalid parameters exist in file complex_del.txt");
			}
		} else {
			System.err
					.println("Invalid input format exists in file complex_del.txt.  Use <property>\\t<tag>");
		}
	}

	/**
	 * Removes simple properties
	 * 
	 * @param orig
	 *            - the full complex string
	 * @param value
	 *            - the tag for the simple string value that we want to retrieve
	 *            from orig
	 * @return the string
	 */
	public String removeData(String orig, String value) {
		String newValue, s1, s2 = new String();
		int pos1 = orig.indexOf("<" + value + ">");
		int pos2 = orig.indexOf("</" + value + ">");
		if (pos1 != -1 && pos2 != -1) {
			s1 = orig.substring(0, pos1);
			s2 = orig.substring(pos2 + 3 + value.length(), orig.length()); // 3
			// is
			// </
			// >
			newValue = s1 + s2;
		} else {
			newValue = orig;
		}
		return newValue;
	}

	/**
	 * Removes the empty properties.
	 */
	public void removeEmpty() {
		try {
			Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();
			for (OWLAxiom ax : ontology.getAxioms()) {
				if (isEmpty(ax)) {
					changes.add(new RemoveAxiom(ontology, ax));
				}
			}
			List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
					changes);
			manager.applyChanges(list);
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Removes the individuals.
	 */
	public void removeIndividuals() {
		try {
			OWLEntityRemover remover = new OWLEntityRemover(manager,
					Collections.singleton(ontology));
			for (OWLIndividual oi : ontology.getReferencedIndividuals()) {
				oi.accept(remover);
			}
			manager.applyChanges(remover.getChanges());
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * This method will remove a given property from the OWL vocabulary. Axioms
	 * to the property are first removed, then the Object/Data property is
	 * removed. Note, axioms within Object or Data properties are not changed.
	 * 
	 * @param property
	 *            the property
	 */
	public void removeProperty(String property) {
		try {
			OWLEntityRemover remover = new OWLEntityRemover(manager,
					Collections.singleton(ontology));
			Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();

			for (OWLAxiom ax : ontology.getAxioms()) {
				if (ax.toString().contains("Annotation(" + property)) {
					changes.add(new RemoveAxiom(ontology, ax));
				}
			}
			List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
					changes);
			manager.applyChanges(list);
			for (OWLDataProperty odp : ontology.getReferencedDataProperties()) {
				if (odp.getURI().toString().equals(
						ontologyNamespace + "#" + property)) {
					odp.accept(remover);
				}
			}
			manager.applyChanges(remover.getChanges());
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Removes a property that has tab characters present.
	 * 
	 * @param property
	 *            the id of the property
	 * @param p
	 *            Property values array, where array elements were determined
	 *            based on tab characters found in the original string
	 * @param pSize
	 *            the string length of the array element
	 */
	public void removeProperty(String property, String[][] p, int pSize) {
		try {
			Set<OWLOntologyChange> changes = new HashSet<OWLOntologyChange>();
			for (OWLAxiom ax : ontology.getAxioms()) {
				if (ax.toString().contains("Annotation(" + property)) {
					boolean remove = true;
					for (int i = 0; i < pSize; i++) {
						// System.out.println(p[i][0] + "\t" + p[i][1]);
						if (!ax.toString().contains(
								"<" + p[i][0] + ">" + p[i][1] + "</" + p[i][0]
										+ ">")) {
							remove = false;
							break;
						}
					}
					if (remove) {
						changes.add(new RemoveAxiom(ontology, ax));
					}
				}
			}
			List<OWLOntologyChange> list = new ArrayList<OWLOntologyChange>(
					changes);
			manager.applyChanges(list);
		} catch (OWLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Run.
	 */
	public void run() {
		try {
			if (!prettyPrint) {

				System.out.println("Removing branches...");
				for (String branch : branchesToDelete) {
					URI branchToDelete = createURI(branch);
					removeBranch(branchToDelete);
				}

				// System.out.println("Simplify complex data...");
				// for (String complex : complexPropsToSimplify) {
				// simplifyComplex(complex);
				// }

				System.out.println("Scrubbing complex data...");
				for (String complex : complexDataToDelete) {
					removeComplex(complex);
				}

				System.out.println("Removing properties...");
				for (String property : propertiesToDelete) {
					if (!property.contains("\t")) {
						removeProperty(property);
					} else {
						String[] values = property.split("\t");
						property = values[0];
						if (values.length % 2 == 1) {
							int pSize = (values.length - 1) / 2;
							String[][] p = new String[pSize][2];
							int pCount = 0;
							for (int i = 1; i < values.length; i++) {
								if (hasLiterals) {
									p[pCount][0] = prefix + values[i];
								} else {
									p[pCount][0] = values[i];
								}
								p[pCount][1] = values[++i]; // we know this
								// works
								pCount++;
							}
							removeProperty(property, p, pSize);

						} else {
							System.out
									.println("Invalid input format exists for property ("
											+ property
											+ ") in file prop_del.txt.");
						}
					}
				}

				fixReferences();
			}

			if (suppressIndividuals) {
				System.out.println("Suppressing Individuals...");
				removeIndividuals();
			}

			if (constructSynonyms) {
				System.out.println("Constructing Synonyms...");
				constructCleanProperty("Synonym", "FULL_SYN", "term-name");
			}

			if (scrubEmpty) {
				System.out.println("Removing empty properties...");
				removeEmpty();
			}

			if (generateFlatFile) {
				System.out.println("Generating flat file...");
				// config_pw("./FlatFile.txt");
				if (config_pw(flatFileURI)) generateFlat();

			}
			System.out.println("Saving...");
			saveOntology();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public Vector<String> getQualifiers(OWLClass c, String property,
			String qualifier) {
		Vector<String> v = new Vector<String>();
		for (OWLAnnotation anno : c.getAnnotations(ontology)) {
			String annotationValue = anno.toString();
			if (annotationValue.contains("Annotation(" + property)) {
				// get property value, return the new value
				int pos1 = annotationValue.indexOf("<" + qualifier + ">");
				int pos2 = annotationValue.indexOf("</" + qualifier + ">");

				if (pos1 != -1 && pos2 != -1) {
					try {
						String value = annotationValue.substring(pos1
								+ qualifier.length() + 2, pos2);
						value = value.replace("&amp;", "&")
								.replace("&lt;", "<");
						if (!v.contains(value)) {
							v.add(value);
						}
					} catch (Exception e) {
						System.out
								.println("Could not parse qualifier value from axiom for concept "
										+ c.toString());
						System.out.println("pos1 = " + pos1
								+ qualifier.length() + 2);
						System.out.println("pos2 = " + (pos2));
						System.out.println(annotationValue);
					}
				}
			}
		}
		return v;
	}

	public String getSolePropertyValue(OWLClass c, String property) {
		String v = new String("");
		for (OWLAnnotation anno : c.getAnnotations(ontology)) {
			String annotationValue = anno.toString();
			if (annotationValue.contains("Annotation(" + property)) {
				// get property value, return the new value
				int beginning = annotationValue.indexOf("(");
				int end = annotationValue.indexOf("^^");
				v = annotationValue.substring(
						beginning + property.length() + 3, end - 1);
				break;
			}
		}
		return v;
	}
	
	public Vector<String> getPropertyValues(OWLClass c, String property) {
		Vector<String> v = new Vector<String>();
		for (OWLAnnotation anno : c.getAnnotations(ontology)) {
			String annotationValue = anno.toString();
			if(annotationValue.contains("Annotation(" + property)) {
				String value;
				int beginning = annotationValue.indexOf("(");
				int end = annotationValue.indexOf("^^");
				value = annotationValue.substring(
						beginning + property.length() + 3, end - 1);
				v.add(value);
			}
		}
		Collections.sort(v);
		return v;
	}

	private boolean isRetired(OWLClass c) {
		boolean retired = false;
		for (OWLAnnotation anno : c.getAnnotations(ontology)) {
			String annotationValue = anno.toString();
			if (annotationValue
					.contains("Annotation(Concept_Status \"Retired_Concept")) {
				retired = true;
				break; // I've seen enough
			}
		}
		return retired;
	}

	public void generateFlat() {
		TreeMap<String, Vector<String>> idAndDatas = new TreeMap<String, Vector<String>>();
		TreeMap<String, Vector<String>> idAndDatasRetired = new TreeMap<String, Vector<String>>();
		OWLClassReasoner reasoner = new ToldClassHierarchyReasoner(manager);
		try {
			reasoner.loadOntologies(Collections.singleton(ontology));
			reasoner.classify();
			for (OWLClass c : ontology.getReferencedClasses()) {
				Set<Set<OWLClass>> parents = reasoner.getSuperClasses(c);
				// Set<OWLDescription> parents = c.getSuperClasses(ontology);
				// Set<OWLDescription> parents2 =
				// c.getEquivalentClasses(ontology);
				// parents.addAll(parents2);
				String code = getSolePropertyValue(c, "code");
				String pn = getSolePropertyValue(c, "Preferred_Name");
				Vector<String> definitions = getQualifiers(c, "DEFINITION",
						prefix + "def-definition");
				Vector<String> terms = getQualifiers(c, "FULL_SYN", prefix
						+ "term-name");
				Vector<String> dns = getPropertyValues(c, "Display_Name");
				Vector<String> stys= getPropertyValues(c, "Semantic_Type");
				Vector<String> statuses = getPropertyValues(c, "Concept_Status");

				if (pn.equals("")) {
					pn = c.asOWLClass().getURI().getFragment();
				}

				// 0- code
				// 1- parents
				// 2- terms
				// 3- definition
				// 4- display_name
				// 5- concept_status
				// 6- semantic_type				
				Vector<String> datas = new Vector<String>();
				Vector<String> parentV = new Vector<String>();
				datas.add(code);

				String parentsString = new String("");
				String termsString = new String(pn);
				String defString = new String("");
				String dnString = new String("");
				String styString = new String("");
				String statusString = new String("");

				for (Set<OWLClass> pSet : parents) {
					for (OWLClass p : pSet) {
						String parCode = getSolePropertyValue(p, "code");
						String par = p.asOWLClass().getURI().getFragment();
						if (par.equals("Thing")) {
							par = "root_node";
						}
						if (parCode != null && parCode.length() > 0) { parentV.add(parCode);}
						else {parentV.add(par);}
					}
				}
				Collections.sort(parentV);
				for (int i = 0; i < parentV.size(); i++) {
					parentsString = parentV.elementAt(i) + "|" + parentsString;
				}
				if (parentsString.contains("|")) {
					parentsString = parentsString.substring(0, parentsString
							.length() - 1);
				}

				// if( parents.size() > 0 ) {
				// OWLDescription[] parArray = parents.toArray(new
				// OWLDescription[parents.size()]);
				// Vector<String> parV = new Vector<String>();
				// for( int i=0; i < parArray.length; i++) {
				// if( !parArray[i].isAnonymous() ) {
				// parV.add(parArray[i].asOWLClass().getURI().getFragment());
				// }
				// }
				// for( int i=0; i < parV.size(); i++ ) {
				// parentsString = parentsString + parV.elementAt(i);
				// if( i != parV.size()-1 ) {
				// parentsString = parentsString + "|";
				// }
				// }
				// }

				datas.add(parentsString);

				while (terms.contains(pn)) {
					terms.remove(pn);
				}
				Collections.sort(terms);
				if (terms.size() > 0) {
					for (int i = 0; i < terms.size(); i++) {
						if (i == 0) {
							termsString = termsString + "|";
						}
						termsString = termsString + terms.elementAt(i);
						if (i != terms.size() - 1) {
							termsString = termsString + "|";
						}
					}
					datas.add(termsString);
				} else {
					datas.add(termsString);
				}

				if (definitions.size() > 0) {
					datas.add(definitions.elementAt(0));
				} else {
					datas.add(defString);
				}
				
				if( dns.size() >= 1 ) {
					for( int i = 0; i < dns.size(); i++) {
						if( i != dns.size() - 1) {
							dnString = dnString + dns.elementAt(i) + "|";
						}
						else {
							dnString = dnString + dns.elementAt(i);
						}
					}
					datas.add(dnString);
				} 
				else {
					datas.add(dnString);
				}
				
				if( statuses.size() >= 1 ) {
					for( int i = 0; i < statuses.size(); i++) {
						if( i != statuses.size() - 1) {
							statusString = statusString + statuses.elementAt(i) + "|";
						}
						else {
							statusString = statusString + statuses.elementAt(i);
						}
					}
					datas.add(statusString);
				}
				else {
					datas.add(statusString);
				}

				if( stys.size() >= 1 ) {
					for( int i = 0; i < stys.size(); i++) {
						if( i != stys.size() - 1) {
							styString = styString + stys.elementAt(i) + "|";
						}
						else {
							styString = styString + stys.elementAt(i);
						}
					}
					datas.add(styString);
				}
				else {
					datas.add(styString);
				}


				// pw.println(datas);
				if (isRetired(c)) {
					idAndDatasRetired.put(c.toString(), datas);
				} else {
					idAndDatas.put(c.toString(), datas);
				}
			}
			for (String key : idAndDatas.keySet()) {
				Vector<String> data = idAndDatas.get(key);
				pw.println(data.elementAt(0) + "\t" + key + "\t"
						+ data.elementAt(1) + "\t" + data.elementAt(2) + "\t"
						+ data.elementAt(3) + "\t" + data.elementAt(4) + "\t"
						+ data.elementAt(5) + "\t" + data.elementAt(6));
				pw.flush();
			}
			for (String key : idAndDatasRetired.keySet()) {
				Vector<String> data = idAndDatasRetired.get(key);
				pw.println(data.elementAt(0) + "\t" + key + "\t"
						+ data.elementAt(1) + "\t" + data.elementAt(2) + "\t"
						+ data.elementAt(3) + "\t" + data.elementAt(4) + "\t"
						+ data.elementAt(5) + "\t" + data.elementAt(6));
				pw.flush();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Save ontology to the file specified in the properties By default encodes
	 * to utf-8
	 */
	private void saveOntology() {
		try {
			RDFXMLOntologyStorer storer = new RDFXMLOntologyStorer();
			File newFile = new File(saveURI);
			FileOutputStream out = new FileOutputStream(newFile);
			WriterOutputTarget target = new WriterOutputTarget(
					new BufferedWriter(new OutputStreamWriter(out, "UTF8")));
			OWLXMLOntologyFormat format = new OWLXMLOntologyFormat();
			if (hasLiterals && prefix.contains("ncicp")) {
				String prefixToAdd = prefix.replace(":", "");
				format
						.addPrefixNamespaceMapping(prefixToAdd,
								"http://ncicb.nci.nih.gov/xml/owl/EVS/ComplexProperties.xsd#");
			}
			storer.storeOntology(manager, ontology, target, format);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

}
