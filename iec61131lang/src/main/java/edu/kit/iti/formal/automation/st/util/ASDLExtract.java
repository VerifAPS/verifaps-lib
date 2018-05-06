package edu.kit.iti.formal.automation.st.util;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import com.google.common.collect.Multimap;
import com.google.common.collect.MultimapBuilder;
import edu.kit.iti.formal.automation.datatypes.values.PointerValue;
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue;
import edu.kit.iti.formal.automation.sfclang.ast.*;
import edu.kit.iti.formal.automation.st.ast.*;

import java.lang.reflect.Field;

/**
 * <p>ECoreXMLGenerator class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ASDLExtract {

    private static Multimap<String, String> hiearchy = MultimapBuilder.hashKeys().arrayListValues().build();
    private static Multimap<String, String> props = MultimapBuilder.hashKeys().arrayListValues().build();
    private Class<? extends Top>[] clazzes;

    /**
     * <p>Constructor for ECoreXMLGenerator.</p>
     *
     * @param clazzes a {@link Class} object.
     */
    @SafeVarargs
    public ASDLExtract(Class<? extends Top>... clazzes) {
        this.clazzes = clazzes;
    }

    /**
     * <p>main.</p>
     *
     * @param args an array of {@link String} objects.
     */
    public static void main(String[] args) {
        new ASDLExtract(
                Top.class,
                VariableDeclaration.class,
                TypeDeclaration.class,
                StructureTypeDeclaration.class,
                StringTypeDeclaration.class,
                SimpleTypeDeclaration.class,
                PointerTypeDeclaration.class,
                EnumerationTypeDeclaration.class,
                SubRangeTypeDeclaration.class,
                ArrayTypeDeclaration.class,
                ReferenceSpecification.class,
                CaseCondition.class,
                CaseCondition.Range.class,
                CaseCondition.Enumeration.class,
                CaseCondition.IntegerCondition.class,
                TopLevelElement.class,
                TypeDeclarations.class,
                TopLevelScopeElement.class,
                CaseStatement.Case.class,
                TopLevelElements.class,
                SFCTransition.class,
                Invocation.Parameter.class,
                SFCImplementation.class,
                SFCStep.class,
                Expression.class,
                Initialization.class,
                Literal.class,
                StructureInitialization.class,
                PointerValue.class,
                Invocation.class,
                ArrayInitialization.class,
                IdentifierInitializer.class,
                ReferenceValue.class,
                Location.class,
                UnaryExpression.class,
                ExpressionList.class,
                Reference.class,
                BinaryExpression.class,
                Statement.class,
                ExitStatement.class,
                AssignmentStatement.class,
                GuardedStatement.class,
                InvocationStatement.class,
                ReturnStatement.class,
                CaseStatement.class,
                ForStatement.class,
                CommentStatement.class,
                IfStatement.class,
                ActionDeclaration.class,
                SFCNetwork.class
        ).run();
    }

    private void run() {
        for (Class<? extends Top> c : clazzes) {
            System.out.println(c.getSimpleName());
            if (c.getSuperclass() != Object.class) {
                hiearchy.put(c.getSuperclass().getSimpleName(), c.getSimpleName());
            }

            for (Field f : c.getDeclaredFields()) {
                Class<?> type = f.getType();
                if (type.getTypeParameters().length != 0)
                    props.put(c.getSimpleName(),
                            String.format("%s* %s",
                                    type.getTypeParameters()[0], f.getName()));
                else
                    props.put(c.getSimpleName(),
                            String.format("%s %s",
                                    type.getSimpleName(), f.getName()));
            }
        }

        print("Top", "");
    }

    private void print(String cur, String indent) {
        if (hiearchy.containsKey(cur)) {
            System.out.format("%n%sgroup(\"%s\") {", indent, cur);
            props.get(cur).forEach(s -> {
                System.out.format("%n%s\tproperty(\"%s\")", indent, s);
            });
            hiearchy.get(cur).forEach(s -> print(s, "\t" + indent));
        } else {
            System.out.format("%n%sleaf(\"%s\") {", indent, cur);
            props.get(cur).forEach(s -> {
                System.out.format("%n%s\tproperty(\"%s\")", indent, s);
            });
        }
        System.out.format("%n%s}", indent);
    }

}
