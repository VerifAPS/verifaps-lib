
package edu.kit.iti.formal.automation.testtables.schema;

import java.util.ArrayList;
import java.util.List;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for variables complex type.
 * 
 * <p>The following schema fragment specifies the expected content contained within this class.
 * 
 * <pre>
 * &lt;complexType name="variables"&gt;
 *   &lt;complexContent&gt;
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType"&gt;
 *       &lt;sequence maxOccurs="unbounded"&gt;
 *         &lt;choice&gt;
 *           &lt;element name="variable" type="{http://formal.iti.kit.edu/exteta-1.1}ioVariable"/&gt;
 *           &lt;element name="constraint" type="{http://formal.iti.kit.edu/exteta-1.1}constraintVariable"/&gt;
 *         &lt;/choice&gt;
 *       &lt;/sequence&gt;
 *     &lt;/restriction&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 * 
 * 
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(name = "variables", propOrder = {
    "variableOrConstraint"
})
public class Variables {

    @XmlElements({
        @XmlElement(name = "variable", type = IoVariable.class),
        @XmlElement(name = "constraint", type = ConstraintVariable.class)
    })
    protected List<Variable> variableOrConstraint;

    /**
     * Gets the value of the variableOrConstraint property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the variableOrConstraint property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getVariableOrConstraint().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link IoVariable }
     * {@link ConstraintVariable }
     * 
     * 
     */
    public List<Variable> getVariableOrConstraint() {
        if (variableOrConstraint == null) {
            variableOrConstraint = new ArrayList<Variable>();
        }
        return this.variableOrConstraint;
    }

}
