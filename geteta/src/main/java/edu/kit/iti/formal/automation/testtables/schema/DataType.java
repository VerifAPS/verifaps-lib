
package edu.kit.iti.formal.automation.testtables.schema;

import javax.xml.bind.annotation.XmlEnum;
import javax.xml.bind.annotation.XmlType;


/**
 * <p>Java class for dataType.
 * 
 * <p>The following schema fragment specifies the expected content contained within this class.
 * <p>
 * <pre>
 * &lt;simpleType name="dataType"&gt;
 *   &lt;restriction base="{http://www.w3.org/2001/XMLSchema}string"&gt;
 *     &lt;enumeration value="ENUM"/&gt;
 *     &lt;enumeration value="INT"/&gt;
 *     &lt;enumeration value="SINT"/&gt;
 *     &lt;enumeration value="LINT"/&gt;
 *     &lt;enumeration value="DINT"/&gt;
 *     &lt;enumeration value="UINT"/&gt;
 *     &lt;enumeration value="UDINT"/&gt;
 *     &lt;enumeration value="ULINT"/&gt;
 *     &lt;enumeration value="USINT"/&gt;
 *     &lt;enumeration value="BOOLEAN"/&gt;
 *     &lt;enumeration value="BYTE"/&gt;
 *     &lt;enumeration value="WORD"/&gt;
 *     &lt;enumeration value="LWORD"/&gt;
 *     &lt;enumeration value="DWORD"/&gt;
 *   &lt;/restriction&gt;
 * &lt;/simpleType&gt;
 * </pre>
 * 
 */
@XmlType(name = "dataType")
@XmlEnum
public enum DataType {

    ENUM,
    INT,
    SINT,
    LINT,
    DINT,
    UINT,
    UDINT,
    ULINT,
    USINT,
    BOOLEAN,
    BYTE,
    WORD,
    LWORD,
    DWORD;

    public String value() {
        return name();
    }

    public static DataType fromValue(String v) {
        return valueOf(v);
    }

}
