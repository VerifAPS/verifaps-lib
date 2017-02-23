//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:33 PM CET 
//


package edu.kit.iti.formal.stvs.logic.io.xml;

import javax.xml.bind.JAXBElement;
import javax.xml.bind.annotation.XmlElementDecl;
import javax.xml.bind.annotation.XmlRegistry;
import javax.xml.namespace.QName;


/**
 * This object contains factory methods for each 
 * Java content interface and Java element interface 
 * generated in the edu.kit.iti.formal.stvs.logic.io.xml package. 
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

    private final static QName _Session_QNAME = new QName("http://formal.iti.kit.edu/stvs/logic/io/xml", "session");
    private final static QName _Specification_QNAME = new QName("http://formal.iti.kit.edu/stvs/logic/io/xml", "specification");
    private final static QName _History_QNAME = new QName("http://formal.iti.kit.edu/stvs/logic/io/xml", "history");
    private final static QName _Config_QNAME = new QName("http://formal.iti.kit.edu/stvs/logic/io/xml", "config");

    /**
     * Create a new ObjectFactory that can be used to create new instances of schema derived classes for package: edu.kit.iti.formal.stvs.logic.io.xml
     * 
     */
    public ObjectFactory() {
    }

    /**
     * Create an instance of {@link Rows }
     * 
     */
    public Rows createRows() {
        return new Rows();
    }

    /**
     * Create an instance of {@link Rows.Row }
     * 
     */
    public Rows.Row createRowsRow() {
        return new Rows.Row();
    }

    /**
     * Create an instance of {@link EnumTypes }
     * 
     */
    public EnumTypes createEnumTypes() {
        return new EnumTypes();
    }

    /**
     * Create an instance of {@link Variables }
     * 
     */
    public Variables createVariables() {
        return new Variables();
    }

    /**
     * Create an instance of {@link Config }
     * 
     */
    public Config createConfig() {
        return new Config();
    }

    /**
     * Create an instance of {@link Config.General }
     * 
     */
    public Config.General createConfigGeneral() {
        return new Config.General();
    }

    /**
     * Create an instance of {@link Session }
     * 
     */
    public Session createSession() {
        return new Session();
    }

    /**
     * Create an instance of {@link SpecificationTable }
     * 
     */
    public SpecificationTable createSpecificationTable() {
        return new SpecificationTable();
    }

    /**
     * Create an instance of {@link Project }
     * 
     */
    public Project createProject() {
        return new Project();
    }

    /**
     * Create an instance of {@link Code }
     * 
     */
    public Code createCode() {
        return new Code();
    }

    /**
     * Create an instance of {@link History }
     * 
     */
    public History createHistory() {
        return new History();
    }

    /**
     * Create an instance of {@link Tab }
     * 
     */
    public Tab createTab() {
        return new Tab();
    }

    /**
     * Create an instance of {@link Rows.Row.Duration }
     * 
     */
    public Rows.Row.Duration createRowsRowDuration() {
        return new Rows.Row.Duration();
    }

    /**
     * Create an instance of {@link Rows.Row.Cell }
     * 
     */
    public Rows.Row.Cell createRowsRowCell() {
        return new Rows.Row.Cell();
    }

    /**
     * Create an instance of {@link Rows.Row.Cycle }
     * 
     */
    public Rows.Row.Cycle createRowsRowCycle() {
        return new Rows.Row.Cycle();
    }

    /**
     * Create an instance of {@link EnumTypes.Enum }
     * 
     */
    public EnumTypes.Enum createEnumTypesEnum() {
        return new EnumTypes.Enum();
    }

    /**
     * Create an instance of {@link Variables.IoVariable }
     * 
     */
    public Variables.IoVariable createVariablesIoVariable() {
        return new Variables.IoVariable();
    }

    /**
     * Create an instance of {@link Variables.FreeVariable }
     * 
     */
    public Variables.FreeVariable createVariablesFreeVariable() {
        return new Variables.FreeVariable();
    }

    /**
     * Create an instance of {@link Config.Editor }
     * 
     */
    public Config.Editor createConfigEditor() {
        return new Config.Editor();
    }

    /**
     * Create an instance of {@link Config.Dependencies }
     * 
     */
    public Config.Dependencies createConfigDependencies() {
        return new Config.Dependencies();
    }

    /**
     * Create an instance of {@link Config.General.WindowSize }
     * 
     */
    public Config.General.WindowSize createConfigGeneralWindowSize() {
        return new Config.General.WindowSize();
    }

    /**
     * Create an instance of {@link Session.Tabs }
     * 
     */
    public Session.Tabs createSessionTabs() {
        return new Session.Tabs();
    }

    /**
     * Create an instance of {@link JAXBElement }{@code <}{@link Session }{@code >}}
     * 
     */
    @XmlElementDecl(namespace = "http://formal.iti.kit.edu/stvs/logic/io/xml", name = "session")
    public JAXBElement<Session> createSession(Session value) {
        return new JAXBElement<Session>(_Session_QNAME, Session.class, null, value);
    }

    /**
     * Create an instance of {@link JAXBElement }{@code <}{@link SpecificationTable }{@code >}}
     * 
     */
    @XmlElementDecl(namespace = "http://formal.iti.kit.edu/stvs/logic/io/xml", name = "specification")
    public JAXBElement<SpecificationTable> createSpecification(SpecificationTable value) {
        return new JAXBElement<SpecificationTable>(_Specification_QNAME, SpecificationTable.class, null, value);
    }

    /**
     * Create an instance of {@link JAXBElement }{@code <}{@link History }{@code >}}
     * 
     */
    @XmlElementDecl(namespace = "http://formal.iti.kit.edu/stvs/logic/io/xml", name = "history")
    public JAXBElement<History> createHistory(History value) {
        return new JAXBElement<History>(_History_QNAME, History.class, null, value);
    }

    /**
     * Create an instance of {@link JAXBElement }{@code <}{@link Config }{@code >}}
     * 
     */
    @XmlElementDecl(namespace = "http://formal.iti.kit.edu/stvs/logic/io/xml", name = "config")
    public JAXBElement<Config> createConfig(Config value) {
        return new JAXBElement<Config>(_Config_QNAME, Config.class, null, value);
    }

}
