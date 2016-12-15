package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Created by weigl on 24.11.16.
 */
public class GlobalScope {
    private Map<String, ProgramDeclaration> programs = new HashMap<>();
    private Map<String, FunctionBlockDeclaration> fb = new HashMap<>();
    private Map<String, FunctionDeclaration> functions = new HashMap<>();
    private Map<String, TypeDeclaration> dataTypes = new HashMap<>();
    private List<FunctionResolver> functionResolvers = new LinkedList<>();
    private TypeScope types = TypeScope.builtin();

    public static GlobalScope defaultScope() {
        GlobalScope g = new GlobalScope();
        g.functionResolvers.add(new DefinedFunctionResolver());
        g.functionResolvers.add(new FunctionResolverMUX());
        return g;
    }

    public ProgramDeclaration getProgram(Object key) {
        return programs.get(key);
    }

    public FunctionBlockDeclaration getFunctionBlock(Object key) {
        return fb.get(key);
    }

    public FunctionDeclaration getFunction(Object key) {
        return functions.get(key);
    }


    public void registerProgram(ProgramDeclaration programDeclaration) {
        programs.put(programDeclaration.getBlockName(), programDeclaration);
    }

    public void registerFunction(FunctionDeclaration functionDeclaration) {
        functions.put(functionDeclaration.getBlockName(), functionDeclaration);
    }

    public void registerFunctionBlock(FunctionBlockDeclaration fblock) {
        fb.put(fblock.getBlockName(), fblock);
    }

    public void registerType(TypeDeclaration dt) {
        dataTypes.put(dt.getTypeName(), dt);
    }

    public Any resolveDataType(String name) {
        if (types.containsKey(name))
            return types.get(name);

        boolean a = fb.containsKey(name);
        boolean b = dataTypes.containsKey(name);
        if (a && b) {
            System.out.println("ambguity fb vs. type");
        }
        Any q;
        if (a) {
            q = new FunctionBlockDataType(fb.get(name));
            types.put(name, q);
            return q;
        }
        if (b) {
            q = dataTypes.get(name).getDataType(this);
            types.put(name, q);
            return q;
        }
        throw new DataTypeNotDefinedException("Could not find: " + name);
    }

    public FunctionDeclaration resolveFunction(FunctionCall functionCall, LocalScope local) {
        for (FunctionResolver fr : functionResolvers) {
            FunctionDeclaration decl = fr.resolve(functionCall, local);
            if (decl != null) return decl;
        }
        return null;
    }
}
