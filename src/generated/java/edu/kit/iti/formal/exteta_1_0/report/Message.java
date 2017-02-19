//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:36 PM CET 
//


package edu.kit.iti.formal.exteta_1_0.report;

import java.util.ArrayList;
import java.util.List;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlType;
import javax.xml.bind.annotation.XmlValue;


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
 *         &lt;element name="log" minOccurs="0">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;sequence>
 *                   &lt;element name="entry" maxOccurs="unbounded" minOccurs="0">
 *                     &lt;complexType>
 *                       &lt;simpleContent>
 *                         &lt;extension base="&lt;http://www.w3.org/2001/XMLSchema>string">
 *                           &lt;attribute name="time" type="{http://www.w3.org/2001/XMLSchema}int" />
 *                           &lt;attribute name="level" type="{http://www.w3.org/2001/XMLSchema}string" />
 *                         &lt;/extension>
 *                       &lt;/simpleContent>
 *                     &lt;/complexType>
 *                   &lt;/element>
 *                 &lt;/sequence>
 *               &lt;/restriction>
 *             &lt;/complexContent>
 *           &lt;/complexType>
 *         &lt;/element>
 *         &lt;element name="counterexample" minOccurs="0">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;all>
 *                   &lt;element name="trace" type="{http://formal.iti.kit.edu/exteta-1.0/report/}counterexample"/>
 *                   &lt;element name="row-mappings" minOccurs="0">
 *                     &lt;complexType>
 *                       &lt;complexContent>
 *                         &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                           &lt;sequence maxOccurs="unbounded">
 *                             &lt;element name="row-map" type="{http://www.w3.org/2001/XMLSchema}string"/>
 *                           &lt;/sequence>
 *                         &lt;/restriction>
 *                       &lt;/complexContent>
 *                     &lt;/complexType>
 *                   &lt;/element>
 *                 &lt;/all>
 *               &lt;/restriction>
 *             &lt;/complexContent>
 *           &lt;/complexType>
 *         &lt;/element>
 *       &lt;/sequence>
 *       &lt;attribute name="returncode" type="{http://www.w3.org/2001/XMLSchema}string" />
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "", propOrder = {
    "log",
    "counterexample"
})
@XmlRootElement(name = "message")
public class Message {

    protected Message.Log log;
    protected Message.Counterexample counterexample;
    @XmlAttribute(name = "returncode")
    protected String returncode;

    /**
     * Ruft den Wert der log-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Message.Log }
     *     
     */
    public Message.Log getLog() {
        return log;
    }

    /**
     * Legt den Wert der log-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Message.Log }
     *     
     */
    public void setLog(Message.Log value) {
        this.log = value;
    }

    /**
     * Ruft den Wert der counterexample-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Message.Counterexample }
     *     
     */
    public Message.Counterexample getCounterexample() {
        return counterexample;
    }

    /**
     * Legt den Wert der counterexample-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Message.Counterexample }
     *     
     */
    public void setCounterexample(Message.Counterexample value) {
        this.counterexample = value;
    }

    /**
     * Ruft den Wert der returncode-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getReturncode() {
        return returncode;
    }

    /**
     * Legt den Wert der returncode-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setReturncode(String value) {
        this.returncode = value;
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
     *       &lt;all>
     *         &lt;element name="trace" type="{http://formal.iti.kit.edu/exteta-1.0/report/}counterexample"/>
     *         &lt;element name="row-mappings" minOccurs="0">
     *           &lt;complexType>
     *             &lt;complexContent>
     *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
     *                 &lt;sequence maxOccurs="unbounded">
     *                   &lt;element name="row-map" type="{http://www.w3.org/2001/XMLSchema}string"/>
     *                 &lt;/sequence>
     *               &lt;/restriction>
     *             &lt;/complexContent>
     *           &lt;/complexType>
     *         &lt;/element>
     *       &lt;/all>
     *     &lt;/restriction>
     *   &lt;/complexContent>
     * &lt;/complexType>
     * </pre>
     * 
     * 
     */
    @XmlAccessorType(XmlAccessType.FIELD)
    @XmlType(name = "", propOrder = {

    })
    public static class Counterexample {

        @XmlElement(required = true)
        protected edu.kit.iti.formal.exteta_1_0.report.Counterexample trace;
        @XmlElement(name = "row-mappings")
        protected Message.Counterexample.RowMappings rowMappings;

        /**
         * Ruft den Wert der trace-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link edu.kit.iti.formal.exteta_1_0.report.Counterexample }
         *     
         */
        public edu.kit.iti.formal.exteta_1_0.report.Counterexample getTrace() {
            return trace;
        }

        /**
         * Legt den Wert der trace-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link edu.kit.iti.formal.exteta_1_0.report.Counterexample }
         *     
         */
        public void setTrace(edu.kit.iti.formal.exteta_1_0.report.Counterexample value) {
            this.trace = value;
        }

        /**
         * Ruft den Wert der rowMappings-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link Message.Counterexample.RowMappings }
         *     
         */
        public Message.Counterexample.RowMappings getRowMappings() {
            return rowMappings;
        }

        /**
         * Legt den Wert der rowMappings-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link Message.Counterexample.RowMappings }
         *     
         */
        public void setRowMappings(Message.Counterexample.RowMappings value) {
            this.rowMappings = value;
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
         *         &lt;element name="row-map" type="{http://www.w3.org/2001/XMLSchema}string"/>
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
            "rowMap"
        })
        public static class RowMappings {

            @XmlElement(name = "row-map", required = true)
            protected List<String> rowMap;

            /**
             * Gets the value of the rowMap property.
             * 
             * <p>
             * This accessor method returns a reference to the live list,
             * not a snapshot. Therefore any modification you make to the
             * returned list will be present inside the JAXB object.
             * This is why there is not a <CODE>set</CODE> method for the rowMap property.
             * 
             * <p>
             * For example, to add a new item, do as follows:
             * <pre>
             *    getRowMap().add(newItem);
             * </pre>
             * 
             * 
             * <p>
             * Objects of the following type(s) are allowed in the list
             * {@link String }
             * 
             * 
             */
            public List<String> getRowMap() {
                if (rowMap == null) {
                    rowMap = new ArrayList<String>();
                }
                return this.rowMap;
            }

        }

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
     *       &lt;sequence>
     *         &lt;element name="entry" maxOccurs="unbounded" minOccurs="0">
     *           &lt;complexType>
     *             &lt;simpleContent>
     *               &lt;extension base="&lt;http://www.w3.org/2001/XMLSchema>string">
     *                 &lt;attribute name="time" type="{http://www.w3.org/2001/XMLSchema}int" />
     *                 &lt;attribute name="level" type="{http://www.w3.org/2001/XMLSchema}string" />
     *               &lt;/extension>
     *             &lt;/simpleContent>
     *           &lt;/complexType>
     *         &lt;/element>
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
        "entry"
    })
    public static class Log {

        protected List<Message.Log.Entry> entry;

        /**
         * Gets the value of the entry property.
         * 
         * <p>
         * This accessor method returns a reference to the live list,
         * not a snapshot. Therefore any modification you make to the
         * returned list will be present inside the JAXB object.
         * This is why there is not a <CODE>set</CODE> method for the entry property.
         * 
         * <p>
         * For example, to add a new item, do as follows:
         * <pre>
         *    getEntry().add(newItem);
         * </pre>
         * 
         * 
         * <p>
         * Objects of the following type(s) are allowed in the list
         * {@link Message.Log.Entry }
         * 
         * 
         */
        public List<Message.Log.Entry> getEntry() {
            if (entry == null) {
                entry = new ArrayList<Message.Log.Entry>();
            }
            return this.entry;
        }


        /**
         * <p>Java-Klasse für anonymous complex type.
         * 
         * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
         * 
         * <pre>
         * &lt;complexType>
         *   &lt;simpleContent>
         *     &lt;extension base="&lt;http://www.w3.org/2001/XMLSchema>string">
         *       &lt;attribute name="time" type="{http://www.w3.org/2001/XMLSchema}int" />
         *       &lt;attribute name="level" type="{http://www.w3.org/2001/XMLSchema}string" />
         *     &lt;/extension>
         *   &lt;/simpleContent>
         * &lt;/complexType>
         * </pre>
         * 
         * 
         */
        @XmlAccessorType(XmlAccessType.FIELD)
        @XmlType(name = "", propOrder = {
            "value"
        })
        public static class Entry {

            @XmlValue
            protected String value;
            @XmlAttribute(name = "time")
            protected Integer time;
            @XmlAttribute(name = "level")
            protected String level;

            /**
             * Ruft den Wert der value-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link String }
             *     
             */
            public String getValue() {
                return value;
            }

            /**
             * Legt den Wert der value-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link String }
             *     
             */
            public void setValue(String value) {
                this.value = value;
            }

            /**
             * Ruft den Wert der time-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link Integer }
             *     
             */
            public Integer getTime() {
                return time;
            }

            /**
             * Legt den Wert der time-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link Integer }
             *     
             */
            public void setTime(Integer value) {
                this.time = value;
            }

            /**
             * Ruft den Wert der level-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link String }
             *     
             */
            public String getLevel() {
                return level;
            }

            /**
             * Legt den Wert der level-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link String }
             *     
             */
            public void setLevel(String value) {
                this.level = value;
            }

        }

    }

}
