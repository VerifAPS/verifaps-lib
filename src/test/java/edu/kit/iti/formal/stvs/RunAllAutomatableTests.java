package edu.kit.iti.formal.stvs;

import com.googlecode.junittoolbox.ExcludeCategories;
import com.googlecode.junittoolbox.SuiteClasses;
import com.googlecode.junittoolbox.WildcardPatternSuite;
import edu.kit.iti.formal.stvs.view.Demo;
import org.junit.experimental.categories.Categories;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Created by csicar on 02.03.17.
 */
@RunWith(WildcardPatternSuite.class)
@SuiteClasses({"**/*Test.class"})
@ExcludeCategories({Demo.class, Performance.class})
public class RunAllAutomatableTests {
}
