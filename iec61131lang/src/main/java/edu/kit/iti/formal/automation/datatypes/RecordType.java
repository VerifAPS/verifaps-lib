package edu.kit.iti.formal.automation.datatypes;

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

import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode
@NoArgsConstructor
@AllArgsConstructor
public class RecordType extends AnyDt {
    private String name;

    @NotNull
    private Scope fields = new Scope();

    /**
     * The declaration associated with the type.
     */
    private TypeDeclaration declaration;

    /**
     * <p>Constructor for RecordType.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public RecordType(@NotNull String name, @NotNull TypeDeclaration declaration) {
        this.name = name;
        this.declaration = declaration;
    }

    /**
     * <p>addField.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public void addField(@NotNull String name, @NotNull AnyDt dataType) {
        fields.add(new VariableDeclaration(name, dataType));
    }

    /** {@inheritDoc} */
    @Nullable
    @Override
    public String repr(Object obj) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(@NotNull DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Deprecated
    public class Field {
        private String name;
        private AnyDt dataType;
        private Object defValue;

        Field(@NotNull String name, @NotNull AnyDt dataType) {
            this.name = name;
            this.dataType = dataType;
        }

        public String getName() {
            return name;
        }

        public void setName(@NotNull String name) {
            this.name = name;
        }

        public AnyDt getDataType() {
            return dataType;
        }

        public void setDataType(@NotNull AnyDt dataType) {
            this.dataType = dataType;
        }

        public Object getDefValue() {
            return defValue;
        }

        public void setDefValue(@NotNull Object defValue) {
            this.defValue = defValue;
        }

    }
}
