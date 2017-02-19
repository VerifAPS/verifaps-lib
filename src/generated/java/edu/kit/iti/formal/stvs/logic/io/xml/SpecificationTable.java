//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:33 PM CET 
//


package edu.kit.iti.formal.stvs.logic.io.xml;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java-Klasse für SpecificationTable complex type.
 * 
 * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
 * 
 * <pre>
 * &lt;complexType name="SpecificationTable">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="variables" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Variables"/>
 *         &lt;element name="rows" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Rows" minOccurs="0"/>
 *         &lt;element name="enumTypes" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}EnumTypes" minOccurs="0"/>
 *       &lt;/sequence>
 *       &lt;attribute name="isConcrete" use="required" type="{http://www.w3.org/2001/XMLSchema}boolean" />
 *       &lt;attribute name="isCounterExample" type="{http://www.w3.org/2001/XMLSchema}boolean" default="false" />
 *       &lt;attribute name="comment" type="{http://www.w3.org/2001/XMLSchema}string" />
 *       &lt;attribute name="name" type="{http://www.w3.org/2001/XMLSchema}string" default="Unnamed Specification" />
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "SpecificationTable", propOrder = {
    "variables",
    "rows",
    "enumTypes"
})
public class SpecificationTable {

    @XmlElement(required = true)
    protected Variables variables;
    protected Rows rows;
    protected EnumTypes enumTypes;
    @XmlAttribute(name = "isConcrete", required = true)
    protected boolean isConcrete;
    @XmlAttribute(name = "isCounterExample")
    protected Boolean isCounterExample;
    @XmlAttribute(name = "comment")
    protected String comment;
    @XmlAttribute(name = "name")
    protected String name;

    /**
     * Ruft den Wert der variables-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Variables }
     *     
     */
    public Variables getVariables() {
        return variables;
    }

    /**
     * Legt den Wert der variables-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Variables }
     *     
     */
    public void setVariables(Variables value) {
        this.variables = value;
    }

    /**
     * Ruft den Wert der rows-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Rows }
     *     
     */
    public Rows getRows() {
        return rows;
    }

    /**
     * Legt den Wert der rows-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Rows }
     *     
     */
    public void setRows(Rows value) {
        this.rows = value;
    }

    /**
     * Ruft den Wert der enumTypes-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link EnumTypes }
     *     
     */
    public EnumTypes getEnumTypes() {
        return enumTypes;
    }

    /**
     * Legt den Wert der enumTypes-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link EnumTypes }
     *     
     */
    public void setEnumTypes(EnumTypes value) {
        this.enumTypes = value;
    }

    /**
     * Ruft den Wert der isConcrete-Eigenschaft ab.
     * 
     */
    public boolean isIsConcrete() {
        return isConcrete;
    }

    /**
     * Legt den Wert der isConcrete-Eigenschaft fest.
     * 
     */
    public void setIsConcrete(boolean value) {
        this.isConcrete = value;
    }

    /**
     * Ruft den Wert der isCounterExample-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Boolean }
     *     
     */
    public boolean isIsCounterExample() {
        if (isCounterExample == null) {
            return false;
        } else {
            return isCounterExample;
        }
    }

    /**
     * Legt den Wert der isCounterExample-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Boolean }
     *     
     */
    public void setIsCounterExample(Boolean value) {
        this.isCounterExample = value;
    }

    /**
     * Ruft den Wert der comment-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getComment() {
        return comment;
    }

    /**
     * Legt den Wert der comment-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setComment(String value) {
        this.comment = value;
    }

    /**
     * Ruft den Wert der name-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getName() {
        if (name == null) {
            return "Unnamed Specification";
        } else {
            return name;
        }
    }

    /**
     * Legt den Wert der name-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setName(String value) {
        this.name = value;
    }

}
