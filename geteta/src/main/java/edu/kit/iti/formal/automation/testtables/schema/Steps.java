
package edu.kit.iti.formal.automation.testtables.schema;

import java.util.ArrayList;
import java.util.List;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for steps complex type.
 * 
 * <p>The following schema fragment specifies the expected content contained within this class.
 * 
 * <pre>
 * &lt;complexType name="steps"&gt;
 *   &lt;complexContent&gt;
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType"&gt;
 *       &lt;sequence maxOccurs="unbounded" minOccurs="0"&gt;
 *         &lt;choice&gt;
 *           &lt;element name="block" type="{http://formal.iti.kit.edu/exteta-1.1}block"/&gt;
 *           &lt;element name="step" type="{http://formal.iti.kit.edu/exteta-1.1}step"/&gt;
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
@XmlType(name = "steps", propOrder = {
    "blockOrStep"
})
public class Steps {

    @XmlElements({
        @XmlElement(name = "block", type = Block.class),
        @XmlElement(name = "step", type = Step.class)
    })
    protected List<Object> blockOrStep;

    /**
     * Gets the value of the blockOrStep property.
     * 
     * <p>
     * This accessor method returns a reference to the live list,
     * not a snapshot. Therefore any modification you make to the
     * returned list will be present inside the JAXB object.
     * This is why there is not a <CODE>set</CODE> method for the blockOrStep property.
     * 
     * <p>
     * For example, to add a new item, do as follows:
     * <pre>
     *    getBlockOrStep().add(newItem);
     * </pre>
     * 
     * 
     * <p>
     * Objects of the following type(s) are allowed in the list
     * {@link Block }
     * {@link Step }
     * 
     * 
     */
    public List<Object> getBlockOrStep() {
        if (blockOrStep == null) {
            blockOrStep = new ArrayList<Object>();
        }
        return this.blockOrStep;
    }

}
