//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:33 PM CET 
//


package edu.kit.iti.formal.stvs.logic.io.xml;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java-Klasse für anonymous complex type.
 * 
 * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
 * 
 * <pre>
 * &lt;complexType>
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="code" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Code"/>
 *         &lt;element name="spec" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}SpecificationTable"/>
 *         &lt;element name="testResult" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}SpecificationTable"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "", propOrder = {
    "code",
    "spec",
    "testResult"
})
@XmlRootElement(name = "project")
public class Project {

    @XmlElement(required = true)
    protected Code code;
    @XmlElement(required = true)
    protected SpecificationTable spec;
    @XmlElement(required = true)
    protected SpecificationTable testResult;

    /**
     * Ruft den Wert der code-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Code }
     *     
     */
    public Code getCode() {
        return code;
    }

    /**
     * Legt den Wert der code-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Code }
     *     
     */
    public void setCode(Code value) {
        this.code = value;
    }

    /**
     * Ruft den Wert der spec-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link SpecificationTable }
     *     
     */
    public SpecificationTable getSpec() {
        return spec;
    }

    /**
     * Legt den Wert der spec-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link SpecificationTable }
     *     
     */
    public void setSpec(SpecificationTable value) {
        this.spec = value;
    }

    /**
     * Ruft den Wert der testResult-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link SpecificationTable }
     *     
     */
    public SpecificationTable getTestResult() {
        return testResult;
    }

    /**
     * Legt den Wert der testResult-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link SpecificationTable }
     *     
     */
    public void setTestResult(SpecificationTable value) {
        this.testResult = value;
    }

}
