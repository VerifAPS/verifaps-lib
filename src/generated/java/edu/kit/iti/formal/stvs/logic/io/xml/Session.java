//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:33 PM CET 
//


package edu.kit.iti.formal.stvs.logic.io.xml;

import java.util.ArrayList;
import java.util.List;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java-Klasse für Session complex type.
 * 
 * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
 * 
 * <pre>
 * &lt;complexType name="Session">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="code" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Code"/>
 *         &lt;element name="tabs">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;sequence maxOccurs="unbounded">
 *                   &lt;element name="tab" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Tab"/>
 *                 &lt;/sequence>
 *               &lt;/restriction>
 *             &lt;/complexContent>
 *           &lt;/complexType>
 *         &lt;/element>
 *         &lt;element name="config" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Config" minOccurs="0"/>
 *         &lt;element name="history" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}History" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "Session", propOrder = {
    "code",
    "tabs",
    "config",
    "history"
})
public class Session {

    @XmlElement(required = true)
    protected Code code;
    @XmlElement(required = true)
    protected Session.Tabs tabs;
    protected Config config;
    protected History history;

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
     * Ruft den Wert der tabs-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Session.Tabs }
     *     
     */
    public Session.Tabs getTabs() {
        return tabs;
    }

    /**
     * Legt den Wert der tabs-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Session.Tabs }
     *     
     */
    public void setTabs(Session.Tabs value) {
        this.tabs = value;
    }

    /**
     * Ruft den Wert der config-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Config }
     *     
     */
    public Config getConfig() {
        return config;
    }

    /**
     * Legt den Wert der config-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Config }
     *     
     */
    public void setConfig(Config value) {
        this.config = value;
    }

    /**
     * Ruft den Wert der history-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link History }
     *     
     */
    public History getHistory() {
        return history;
    }

    /**
     * Legt den Wert der history-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link History }
     *     
     */
    public void setHistory(History value) {
        this.history = value;
    }


    /**
     * <p>Java-Klasse für anonymous complex type.
     * 
     * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
     * 
     * <pre>
     * &lt;complexType>
     *   &lt;complexContent>
     *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
     *       &lt;sequence maxOccurs="unbounded">
     *         &lt;element name="tab" type="{http://formal.iti.kit.edu/stvs/logic/io/xml}Tab"/>
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
        "tab"
    })
    public static class Tabs {

        @XmlElement(required = true)
        protected List<Tab> tab;

        /**
         * Gets the value of the tab property.
         * 
         * <p>
         * This accessor method returns a reference to the live list,
         * not a snapshot. Therefore any modification you make to the
         * returned list will be present inside the JAXB object.
         * This is why there is not a <CODE>set</CODE> method for the tab property.
         * 
         * <p>
         * For example, to add a new item, do as follows:
         * <pre>
         *    getTab().add(newItem);
         * </pre>
         * 
         * 
         * <p>
         * Objects of the following type(s) are allowed in the list
         * {@link Tab }
         * 
         * 
         */
        public List<Tab> getTab() {
            if (tab == null) {
                tab = new ArrayList<Tab>();
            }
            return this.tab;
        }

    }

}
