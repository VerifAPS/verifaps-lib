
package edu.kit.iti.formal.automation.testtables.report;

import javax.xml.bind.annotation.XmlRegistry;


/**
 * This object contains factory methods for each 
 * Java content interface and Java element interface 
 * generated in the edu.kit.iti.formal.automation.testtables.report package. 
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


    /**
     * Create a new ObjectFactory that can be used to create new instances of schema derived classes for package: edu.kit.iti.formal.automation.testtables.report
     * 
     */
    public ObjectFactory() {
    }

    /**
     * Create an instance of {@link Message }
     * 
     */
    public Message createMessage() {
        return new Message();
    }

    /**
     * Create an instance of {@link edu.kit.iti.formal.automation.testtables.report.Counterexample }
     * 
     */
    public edu.kit.iti.formal.automation.testtables.report.Counterexample createCounterexample() {
        return new edu.kit.iti.formal.automation.testtables.report.Counterexample();
    }

    /**
     * Create an instance of {@link Message.Counterexample }
     * 
     */
    public Message.Counterexample createMessageCounterexample() {
        return new Message.Counterexample();
    }

    /**
     * Create an instance of {@link Message.Log }
     * 
     */
    public Message.Log createMessageLog() {
        return new Message.Log();
    }

    /**
     * Create an instance of {@link Assignment }
     * 
     */
    public Assignment createAssignment() {
        return new Assignment();
    }

    /**
     * Create an instance of {@link edu.kit.iti.formal.automation.testtables.report.Counterexample.Step }
     * 
     */
    public edu.kit.iti.formal.automation.testtables.report.Counterexample.Step createCounterexampleStep() {
        return new edu.kit.iti.formal.automation.testtables.report.Counterexample.Step();
    }

    /**
     * Create an instance of {@link Message.Counterexample.RowMappings }
     * 
     */
    public Message.Counterexample.RowMappings createMessageCounterexampleRowMappings() {
        return new Message.Counterexample.RowMappings();
    }

    /**
     * Create an instance of {@link Message.Log.Entry }
     * 
     */
    public Message.Log.Entry createMessageLogEntry() {
        return new Message.Log.Entry();
    }

}