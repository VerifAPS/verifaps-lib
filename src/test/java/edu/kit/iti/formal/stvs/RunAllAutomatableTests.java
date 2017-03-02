package edu.kit.iti.formal.stvs;

import com.googlecode.junittoolbox.ExcludeCategories;
import com.googlecode.junittoolbox.SuiteClasses;
import com.googlecode.junittoolbox.WildcardPatternSuite;
import org.junit.runner.RunWith;

/**
 * Created by csicar on 02.03.17.
 */
@RunWith(WildcardPatternSuite.class)
@SuiteClasses({"**/*Test.class"})
@ExcludeCategories({Demo.class, Performance.class})
public class RunAllAutomatableTests {
}
