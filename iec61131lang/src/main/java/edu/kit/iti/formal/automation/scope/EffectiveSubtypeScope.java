package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.ast.MethodDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.Tuple;
import org.jetbrains.annotations.NotNull;

import java.util.*;

public class EffectiveSubtypeScope extends HashMap<Tuple<String, String>, Set<AnyDt>> {
    public void registerVariable(@NotNull VariableDeclaration variable) {
        if (!containsKey(tuple(variable, variable.getParent())))
            put(tuple(variable, variable.getParent()), new HashSet<>());
    }

    public void registerType(@NotNull VariableDeclaration variable, @NotNull AnyDt dataType) {
        get(tuple(variable, variable.getParent())).add(dataType);
    }

    public void registerTypes(@NotNull VariableDeclaration variable, @NotNull Collection<AnyDt> dataTypes) {
        dataTypes.forEach(dt -> registerType(variable, dt));
    }

    public Set<AnyDt> getTypes(@NotNull VariableDeclaration variable) {
        Set<AnyDt> types = get(tuple(variable, variable.getParent()));
        if (types == null)
            throw new NoSuchElementException(tuple(variable, variable.getParent()).toString());
        return types;
    }

    private Tuple<String, String> tuple(@NotNull Identifiable variable, @NotNull Identifiable parent) {
        return new Tuple<>(variable.getIdentifier(),
                parent instanceof MethodDeclaration
                        ? ((MethodDeclaration) parent).getParent().getIdentifier()
                        : parent.getIdentifier());
    }
}
