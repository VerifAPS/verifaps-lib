package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.ast.TopLevelScopeElement;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import javafx.util.Pair;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Set;

public class EffectiveSubtypeScope extends HashMap<Pair<String, String>, Set<Any>> {
    public void registerType(@NotNull TopLevelScopeElement tle, @NotNull VariableDeclaration variable,
                             @NotNull Any dataType) {
        if (!containsKey(pair(tle, variable)))
            put(pair(tle, variable), new HashSet<>());
        get(pair(tle, variable)).add(dataType);
    }

    @NotNull
    public Set<Any> getTypes(TopLevelScopeElement tle, VariableDeclaration variable) {
        Set<Any> types = get(pair(tle, variable));
        if (types == null)
            throw new NoSuchElementException(tle.getIdentifier() + " " + variable.getName());
        return types;
    }

    @NotNull
    private Pair<String, String> pair(@NotNull Identifiable i1, @NotNull Identifiable i2) {
        return new Pair<>(i1.getIdentifier(), i2.getIdentifier());
    }
}
