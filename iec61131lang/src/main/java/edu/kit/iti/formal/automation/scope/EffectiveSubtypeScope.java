package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.ast.MethodDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import javafx.util.Pair;
import org.jetbrains.annotations.NotNull;

import java.util.*;

public class EffectiveSubtypeScope extends HashMap<Pair<String, String>, Set<Any>> {
    public void registerVariable(@NotNull VariableDeclaration variable) {
        if (!containsKey(pair(variable, variable.getParent())))
            put(pair(variable, variable.getParent()), new HashSet<>());
    }

    public void registerType(@NotNull VariableDeclaration variable, @NotNull Any dataType) {
        get(pair(variable, variable.getParent())).add(dataType);
    }

    public void registerTypes(@NotNull VariableDeclaration variable, @NotNull Collection<Any> dataTypes) {
        dataTypes.forEach(dt -> registerType(variable, dt));
    }

    public Set<Any> getTypes(VariableDeclaration variable) {
        Set<Any> types = get(pair(variable, variable.getParent()));
        if (types == null)
            throw new NoSuchElementException(pair(variable, variable.getParent()).toString());
        return types;
    }

    private Pair<String, String> pair(@NotNull Identifiable variable, @NotNull Identifiable parent) {
        return new Pair<>(variable.getIdentifier(),
                parent instanceof MethodDeclaration
                        ? ((MethodDeclaration) parent).getParent().getIdentifier()
                        : parent.getIdentifier());
    }
}
