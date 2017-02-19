//
// Diese Datei wurde mit der JavaTM Architecture for XML Binding(JAXB) Reference Implementation, v2.2.7-b41 generiert 
// Siehe <a href="http://java.sun.com/xml/jaxb">http://java.sun.com/xml/jaxb</a> 
// Änderungen an dieser Datei gehen bei einer Neukompilierung des Quellschemas verloren. 
// Generiert: 2017.02.19 um 01:09:33 PM CET 
//


package edu.kit.iti.formal.stvs.logic.io.xml;

import java.math.BigInteger;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlSchemaType;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java-Klasse für Config complex type.
 * 
 * <p>Das folgende Schemafragment gibt den erwarteten Content an, der in dieser Klasse enthalten ist.
 * 
 * <pre>
 * &lt;complexType name="Config">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="general" minOccurs="0">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;sequence>
 *                   &lt;element name="uiLanguage" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
 *                   &lt;element name="windowSize" minOccurs="0">
 *                     &lt;complexType>
 *                       &lt;complexContent>
 *                         &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                           &lt;sequence>
 *                             &lt;element name="width" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                             &lt;element name="height" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                             &lt;element name="maximized" type="{http://www.w3.org/2001/XMLSchema}boolean" minOccurs="0"/>
 *                           &lt;/sequence>
 *                         &lt;/restriction>
 *                       &lt;/complexContent>
 *                     &lt;/complexType>
 *                   &lt;/element>
 *                   &lt;element name="verificationTimeout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                   &lt;element name="simulationTimeout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                   &lt;element name="maxLineRollout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                 &lt;/sequence>
 *               &lt;/restriction>
 *             &lt;/complexContent>
 *           &lt;/complexType>
 *         &lt;/element>
 *         &lt;element name="editor" minOccurs="0">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;sequence>
 *                   &lt;element name="showLineNumbers" type="{http://www.w3.org/2001/XMLSchema}boolean" minOccurs="0"/>
 *                   &lt;element name="fontFamily" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
 *                   &lt;element name="fontSize" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
 *                 &lt;/sequence>
 *               &lt;/restriction>
 *             &lt;/complexContent>
 *           &lt;/complexType>
 *         &lt;/element>
 *         &lt;element name="dependencies" minOccurs="0">
 *           &lt;complexType>
 *             &lt;complexContent>
 *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *                 &lt;sequence>
 *                   &lt;element name="z3Path" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
 *                   &lt;element name="getetaCommand" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
 *                   &lt;element name="nuxmvFilename" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
 *                 &lt;/sequence>
 *               &lt;/restriction>
 *             &lt;/complexContent>
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
@XmlType(name = "Config", propOrder = {
    "general",
    "editor",
    "dependencies"
})
public class Config {

    protected Config.General general;
    protected Config.Editor editor;
    protected Config.Dependencies dependencies;

    /**
     * Ruft den Wert der general-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Config.General }
     *     
     */
    public Config.General getGeneral() {
        return general;
    }

    /**
     * Legt den Wert der general-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Config.General }
     *     
     */
    public void setGeneral(Config.General value) {
        this.general = value;
    }

    /**
     * Ruft den Wert der editor-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Config.Editor }
     *     
     */
    public Config.Editor getEditor() {
        return editor;
    }

    /**
     * Legt den Wert der editor-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Config.Editor }
     *     
     */
    public void setEditor(Config.Editor value) {
        this.editor = value;
    }

    /**
     * Ruft den Wert der dependencies-Eigenschaft ab.
     * 
     * @return
     *     possible object is
     *     {@link Config.Dependencies }
     *     
     */
    public Config.Dependencies getDependencies() {
        return dependencies;
    }

    /**
     * Legt den Wert der dependencies-Eigenschaft fest.
     * 
     * @param value
     *     allowed object is
     *     {@link Config.Dependencies }
     *     
     */
    public void setDependencies(Config.Dependencies value) {
        this.dependencies = value;
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
     *         &lt;element name="z3Path" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
     *         &lt;element name="getetaCommand" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
     *         &lt;element name="nuxmvFilename" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
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
        "z3Path",
        "getetaCommand",
        "nuxmvFilename"
    })
    public static class Dependencies {

        protected String z3Path;
        protected String getetaCommand;
        protected String nuxmvFilename;

        /**
         * Ruft den Wert der z3Path-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link String }
         *     
         */
        public String getZ3Path() {
            return z3Path;
        }

        /**
         * Legt den Wert der z3Path-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link String }
         *     
         */
        public void setZ3Path(String value) {
            this.z3Path = value;
        }

        /**
         * Ruft den Wert der getetaCommand-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link String }
         *     
         */
        public String getGetetaCommand() {
            return getetaCommand;
        }

        /**
         * Legt den Wert der getetaCommand-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link String }
         *     
         */
        public void setGetetaCommand(String value) {
            this.getetaCommand = value;
        }

        /**
         * Ruft den Wert der nuxmvFilename-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link String }
         *     
         */
        public String getNuxmvFilename() {
            return nuxmvFilename;
        }

        /**
         * Legt den Wert der nuxmvFilename-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link String }
         *     
         */
        public void setNuxmvFilename(String value) {
            this.nuxmvFilename = value;
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
     *         &lt;element name="showLineNumbers" type="{http://www.w3.org/2001/XMLSchema}boolean" minOccurs="0"/>
     *         &lt;element name="fontFamily" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
     *         &lt;element name="fontSize" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
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
        "showLineNumbers",
        "fontFamily",
        "fontSize"
    })
    public static class Editor {

        @XmlElement(defaultValue = "true")
        protected Boolean showLineNumbers;
        protected String fontFamily;
        @XmlSchemaType(name = "positiveInteger")
        protected BigInteger fontSize;

        /**
         * Ruft den Wert der showLineNumbers-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link Boolean }
         *     
         */
        public Boolean isShowLineNumbers() {
            return showLineNumbers;
        }

        /**
         * Legt den Wert der showLineNumbers-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link Boolean }
         *     
         */
        public void setShowLineNumbers(Boolean value) {
            this.showLineNumbers = value;
        }

        /**
         * Ruft den Wert der fontFamily-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link String }
         *     
         */
        public String getFontFamily() {
            return fontFamily;
        }

        /**
         * Legt den Wert der fontFamily-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link String }
         *     
         */
        public void setFontFamily(String value) {
            this.fontFamily = value;
        }

        /**
         * Ruft den Wert der fontSize-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link BigInteger }
         *     
         */
        public BigInteger getFontSize() {
            return fontSize;
        }

        /**
         * Legt den Wert der fontSize-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link BigInteger }
         *     
         */
        public void setFontSize(BigInteger value) {
            this.fontSize = value;
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
     *         &lt;element name="uiLanguage" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/>
     *         &lt;element name="windowSize" minOccurs="0">
     *           &lt;complexType>
     *             &lt;complexContent>
     *               &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
     *                 &lt;sequence>
     *                   &lt;element name="width" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
     *                   &lt;element name="height" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
     *                   &lt;element name="maximized" type="{http://www.w3.org/2001/XMLSchema}boolean" minOccurs="0"/>
     *                 &lt;/sequence>
     *               &lt;/restriction>
     *             &lt;/complexContent>
     *           &lt;/complexType>
     *         &lt;/element>
     *         &lt;element name="verificationTimeout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
     *         &lt;element name="simulationTimeout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
     *         &lt;element name="maxLineRollout" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
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
        "uiLanguage",
        "windowSize",
        "verificationTimeout",
        "simulationTimeout",
        "maxLineRollout"
    })
    public static class General {

        protected String uiLanguage;
        protected Config.General.WindowSize windowSize;
        @XmlSchemaType(name = "positiveInteger")
        protected BigInteger verificationTimeout;
        @XmlSchemaType(name = "positiveInteger")
        protected BigInteger simulationTimeout;
        @XmlSchemaType(name = "positiveInteger")
        protected BigInteger maxLineRollout;

        /**
         * Ruft den Wert der uiLanguage-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link String }
         *     
         */
        public String getUiLanguage() {
            return uiLanguage;
        }

        /**
         * Legt den Wert der uiLanguage-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link String }
         *     
         */
        public void setUiLanguage(String value) {
            this.uiLanguage = value;
        }

        /**
         * Ruft den Wert der windowSize-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link Config.General.WindowSize }
         *     
         */
        public Config.General.WindowSize getWindowSize() {
            return windowSize;
        }

        /**
         * Legt den Wert der windowSize-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link Config.General.WindowSize }
         *     
         */
        public void setWindowSize(Config.General.WindowSize value) {
            this.windowSize = value;
        }

        /**
         * Ruft den Wert der verificationTimeout-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link BigInteger }
         *     
         */
        public BigInteger getVerificationTimeout() {
            return verificationTimeout;
        }

        /**
         * Legt den Wert der verificationTimeout-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link BigInteger }
         *     
         */
        public void setVerificationTimeout(BigInteger value) {
            this.verificationTimeout = value;
        }

        /**
         * Ruft den Wert der simulationTimeout-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link BigInteger }
         *     
         */
        public BigInteger getSimulationTimeout() {
            return simulationTimeout;
        }

        /**
         * Legt den Wert der simulationTimeout-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link BigInteger }
         *     
         */
        public void setSimulationTimeout(BigInteger value) {
            this.simulationTimeout = value;
        }

        /**
         * Ruft den Wert der maxLineRollout-Eigenschaft ab.
         * 
         * @return
         *     possible object is
         *     {@link BigInteger }
         *     
         */
        public BigInteger getMaxLineRollout() {
            return maxLineRollout;
        }

        /**
         * Legt den Wert der maxLineRollout-Eigenschaft fest.
         * 
         * @param value
         *     allowed object is
         *     {@link BigInteger }
         *     
         */
        public void setMaxLineRollout(BigInteger value) {
            this.maxLineRollout = value;
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
         *         &lt;element name="width" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
         *         &lt;element name="height" type="{http://www.w3.org/2001/XMLSchema}positiveInteger" minOccurs="0"/>
         *         &lt;element name="maximized" type="{http://www.w3.org/2001/XMLSchema}boolean" minOccurs="0"/>
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
            "width",
            "height",
            "maximized"
        })
        public static class WindowSize {

            @XmlSchemaType(name = "positiveInteger")
            protected BigInteger width;
            @XmlSchemaType(name = "positiveInteger")
            protected BigInteger height;
            protected Boolean maximized;

            /**
             * Ruft den Wert der width-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link BigInteger }
             *     
             */
            public BigInteger getWidth() {
                return width;
            }

            /**
             * Legt den Wert der width-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link BigInteger }
             *     
             */
            public void setWidth(BigInteger value) {
                this.width = value;
            }

            /**
             * Ruft den Wert der height-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link BigInteger }
             *     
             */
            public BigInteger getHeight() {
                return height;
            }

            /**
             * Legt den Wert der height-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link BigInteger }
             *     
             */
            public void setHeight(BigInteger value) {
                this.height = value;
            }

            /**
             * Ruft den Wert der maximized-Eigenschaft ab.
             * 
             * @return
             *     possible object is
             *     {@link Boolean }
             *     
             */
            public Boolean isMaximized() {
                return maximized;
            }

            /**
             * Legt den Wert der maximized-Eigenschaft fest.
             * 
             * @param value
             *     allowed object is
             *     {@link Boolean }
             *     
             */
            public void setMaximized(Boolean value) {
                this.maximized = value;
            }

        }

    }

}
