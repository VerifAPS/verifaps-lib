package edu.kit.iti.formal.automation
/*
package edu.kit.iti.formal.automation;

import com.google.common.base.CaseFormat;
import edu.kit.iti.formal.automation.oo.OOIEC61131Facade;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.PouElement;
import edu.kit.iti.formal.automation.st.ast.PouElements;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import edu.kit.iti.formal.automation.stoo.trans.STOOTransformation;
import org.junit.Assert;
 import org.junit.jupiter.api.Test;
;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
@RunWith(Parameterized.class)
public class STOOUnitTests {
    private static final String RESOURCES_PATH = "edu/kit/iti/formal/automation/st/stoo/unit";

    @Parameterized.Parameter
    public Class<? extends STOOTransformation> stooTransformation;

    @Parameterized.Parameter(1)
    public File file;

    private static File[] getSTFiles(String folder) {
        URL f = STOOUnitTests.class.getClassLoader().getResource(folder);
        if (f == null) {
            System.err.format("Could not find %s%n", folder);
            return new File[0];
        }
        File file = new File(f.getFile());
        return Arrays.stream(Objects.requireNonNull(file.listFiles()))
                .filter(s -> !s.getName().contains(".stoo")).toArray(File[]::new);
    }

    private static STOOSimplifier.State processSTFile(File f) throws IOException {
        PouElements pouElements =  IEC61131Facade.INSTANCE.file(f);
        Scope globalScope = IEC61131Facade.INSTANCE.resolveDataTypes(pouElements);
        PouElement program = edu.kit.iti.formal.automation.visitors.Utils.INSTANCE.findProgram(pouElements);
        InstanceScope instanceScope = OOIEC61131Facade.INSTANCE.findInstances(program, globalScope);
        EffectiveSubtypeScope effectiveSubtypeScope =
            OOIEC61131Facade.INSTANCE.findEffectiveSubtypes(pouElements, globalScope, instanceScope);
        return new STOOSimplifier.State(program, pouElements, globalScope, instanceScope, effectiveSubtypeScope);
    }

    private static STOOSimplifier.State processSTFile(Path path) throws IOException {
        return processSTFile(path.toFile());
    }

    @Parameterized.Parameters
    public static List<Object[]> stooTransformations() {
        return STOOSimplifier.TRANSFORMATIONS.stream()
                .flatMap(t -> Arrays.stream(getSTFiles(RESOURCES_PATH + "/"
                        + CaseFormat.UPPER_CAMEL.to(CaseFormat.LOWER_UNDERSCORE, t.getSimpleName())))
                        .map(f -> new Object[] {t, f}))
                .collect(Collectors.toList());
    }

    @Test
    public void testSTOOTransformation() throws IOException, IllegalAccessException, InstantiationException {
        STOOTransformation uut = stooTransformation.newInstance();

        System.out.println(uut.getClass().getSimpleName());
        System.out.println(file.getName());

        STOOSimplifier.State st = processSTFile(file);
        PouElements st1Expected = processSTFile(Paths.get(file.toPath() + "oo")).getTopLevelElements();

        uut.transform(st);
        PouElements st1Actual = st.getTopLevelElements();

        Collections.sort(st1Actual);
        Collections.sort(st1Expected);

        Assertions.assertEquals(IEC61131Facade.INSTANCE.printf(st1Expected), IEC61131Facade.INSTANCE.printf(st1Actual));
    }
}
*/