//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:35 PM CET 
//


package edu.kit.iti.formal.exteta_1;

import javax.xml.bind.JAXBElement;
import javax.xml.bind.annotation.XmlElementDecl;
import javax.xml.bind.annotation.XmlRegistry;
import javax.xml.namespace.QName;


/**
 * This object contains factory methods for each 
 * Java content interface and Java element interface 
 * generated in the edu.kit.iti.formal.exteta_1 package. 
 * <p>An ObjectFactory allows you to programatically 
 * construct new instances of the Java representation 
 * for XML content. The Java representation of XML 
 * content can consist of schema derived interfaces 
 * and classes representing the binding of schema 
 * type definitions, element declarations and model 
 * groups.  Factory methods for each of these are 
 * provided in this class.
 * 
 */
@XmlRegistry
public class ObjectFactory {

    private final static QName _TestTable_QNAME = new QName("http://formal.iti.kit.edu/exteta-1.0", "test-table");

    /**
     * Create a new ObjectFactory that can be used to create new instances of schema derived classes for package: edu.kit.iti.formal.exteta_1
     * 
     */
    public ObjectFactory() {
    }

    /**
     * Create an instance of {@link Options }
     * 
     */
    public Options createOptions() {
        return new Options();
    }

    /**
     * Create an instance of {@link TestTable }
     * 
     */
    public TestTable createTestTable() {
        return new TestTable();
    }

    /**
     * Create an instance of {@link Variables }
     * 
     */
    public Variables createVariables() {
        return new Variables();
    }

    /**
     * Create an instance of {@link IoVariable }
     * 
     */
    public IoVariable createIoVariable() {
        return new IoVariable();
    }

    /**
     * Create an instance of {@link Variable }
     * 
     */
    public Variable createVariable() {
        return new Variable();
    }

    /**
     * Create an instance of {@link Step }
     * 
     */
    public Step createStep() {
        return new Step();
    }

    /**
     * Create an instance of {@link Block }
     * 
     */
    public Block createBlock() {
        return new Block();
    }

    /**
     * Create an instance of {@link ConstraintVariable }
     * 
     */
    public ConstraintVariable createConstraintVariable() {
        return new ConstraintVariable();
    }

    /**
     * Create an instance of {@link Steps }
     * 
     */
    public Steps createSteps() {
        return new Steps();
    }

    /**
     * Create an instance of {@link Options.Option }
     * 
     */
    public Options.Option createOptionsOption() {
        return new Options.Option();
    }

    /**
     * Create an instance of {@link JAXBElement }{@code <}{@link TestTable }{@code >}}
     * 
     */
    @XmlElementDecl(namespace = "http://formal.iti.kit.edu/exteta-1.0", name = "test-table")
    public JAXBElement<TestTable> createTestTable(TestTable value) {
        return new JAXBElement<TestTable>(_TestTable_QNAME, TestTable.class, null, value);
    }

}
