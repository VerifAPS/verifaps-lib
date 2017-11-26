package edu.kit.iti.formal.automation.datatypes;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import lombok.AllArgsConstructor;
import lombok.Data;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * This data type represents a class.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 04.03.17
 */
@Data
@AllArgsConstructor
public class ClassDataType extends RecordType {
    @NotNull
    private final ClassDeclaration clazz;

    @Nullable
    @Override public String repr(Object obj) {
        return null;
    }

    @Override
    public <T> T accept(@NotNull DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String getName() {
        return clazz.getName();
    }

    @NotNull
    public ClassDeclaration getClazz() {
        return clazz;
    }

    @Override
    public List<Field> getFields() {
        return clazz.getEffectiveLocalScope().stream()
                .map(v -> new Field(v.getName(), v.getDataType()))
                .collect(Collectors.toList());
    }
}
