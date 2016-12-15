package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.SMVType;
import junit.framework.Assert;
import org.junit.Test;

import java.util.Arrays;

/**
 * @author Alexander Weigl
 * @version 1 (15.12.16)
 */
public class TypeTest {
    @Test
    public void testOutput() {
        SMVType.SMVTypeWithWidth u10 = new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 10);
        SMVType.SMVTypeWithWidth s0 = new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 0);
        SMVType b = new SMVType();
        SMVType.EnumType e = new SMVType.EnumType(Arrays.asList("a", "b", "c"));

        Assert.assertEquals("unsigned word[10]", u10.toString());
        Assert.assertEquals("boolean", b.toString());
        Assert.assertEquals("signed word[0]", s0.toString());
        Assert.assertEquals("{a, b, c}", e.toString());


    }

}
