
package edu.kit.iti.formal.automation.testtables.schema;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for ioVariable complex type.
 * 
 * <p>The following schema fragment specifies the expected content contained within this class.
 * 
 * <pre>
 * &lt;complexType name="ioVariable"&gt;
 *   &lt;complexContent&gt;
 *     &lt;extension base="{http://formal.iti.kit.edu/exteta-1.1}variable"&gt;
 *       &lt;attribute name="io" use="required"&gt;
 *         &lt;simpleType&gt;
 *           &lt;restriction base="{http://www.w3.org/2001/XMLSchema}string"&gt;
 *             &lt;enumeration value="input"/&gt;
 *             &lt;enumeration value="output"/&gt;
 *           &lt;/restriction&gt;
 *         &lt;/simpleType&gt;
 *       &lt;/attribute&gt;
 *     &lt;/extension&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "ioVariable")
public class IoVariable
    extends Variable
{

    @XmlAttribute(name = "io", required = true)
    protected String io;

    /**
     * Gets the value of the io property.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getIo() {
        return io;
    }

    /**
     * Sets the value of the io property.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setIo(String value) {
        this.io = value;
    }

}
