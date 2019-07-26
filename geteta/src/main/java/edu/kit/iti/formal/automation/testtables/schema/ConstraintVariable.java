
package edu.kit.iti.formal.automation.testtables.schema;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for constraintVariable complex type.
 * 
 * <p>The following schema fragment specifies the expected content contained within this class.
 * 
 * <pre>
 * &lt;complexType name="constraintVariable"&gt;
 *   &lt;complexContent&gt;
 *     &lt;extension base="{http://formal.iti.kit.edu/exteta-1.1}variable"&gt;
 *       &lt;attribute name="constraint" type="{http://www.w3.org/2001/XMLSchema}string" default="-" /&gt;
 *     &lt;/extension&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "constraintVariable")
public class ConstraintVariable
    extends Variable
{

    @XmlAttribute(name = "constraint")
    protected String constraint;

    /**
     * Gets the value of the constraint property.
     * 
     * @return
     *     possible object is
     *     {@link String }
     *     
     */
    public String getConstraint() {
        if (constraint == null) {
            return "-";
        } else {
            return constraint;
        }
    }

    /**
     * Sets the value of the constraint property.
     * 
     * @param value
     *     allowed object is
     *     {@link String }
     *     
     */
    public void setConstraint(String value) {
        this.constraint = value;
    }

}
