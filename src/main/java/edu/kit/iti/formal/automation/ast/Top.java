package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import org.antlr.v4.runtime.Token;

import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

public abstract class Top implements Visitable {
    private int lineNumber = -1;
    private int positioninLine = -1;

    public int getLineNumber() {
        return lineNumber;
    }

    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }

    private static void toString(Object o, Class<?> clazz, Map<String, Object> list) {
        Field f[] = clazz.getDeclaredFields();
        AccessibleObject.setAccessible(f, true);

        if (clazz.getSuperclass().getSuperclass() != null) {
            toString(o, clazz.getSuperclass(), list);
        }

        for (int i = 0; i < f.length; i++) {
            try {
                list.put(f[i].getName(), f[i].get(o));
            } catch (IllegalAccessException e) {
                e.printStackTrace();
            }
        }
    }

    public String getNodeName() {
        return getClass().getName();
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(0, sb);
        return sb.toString();
    }

    protected void toString(int indent, StringBuilder sb) {
        Map<String, Object> fields = new HashMap<>();
        Top.toString(this, getClass(), fields);

        sb.append("(").append(getClass().getSimpleName()).append("\n");

        for (Map.Entry<String, Object> e : fields.entrySet()) {
            String tab = repeat(" ", indent + e.getKey().length());
            sb.append(tab).append(':').append(e.getKey()).append(' ');
            if (e.getValue() instanceof Top) {
                Top a = (Top) e.getValue();
                a.toString(indent + 3 + e.getKey().length(), sb);
            } else {
                sb.append(e.getValue());
            }
            sb.append("\n");
        }
        sb.setLength(sb.length() - 1);

        sb.append(")");

    }

    public static String repeat(String str, int times) {
    	StringBuilder sb = new StringBuilder();
    	for (int i = 0; i < times; i++) {
			sb.append(str);
		}
    	return sb.toString();
    }

	public abstract <T> T visit(Visitor<T> visitor);

    public void line(Token aReturn) {
        setLineNumber(aReturn.getLine());
        setPositionInLine(aReturn.getCharPositionInLine());
    }

    public void setPositionInLine(int positioninLine) {
        this.positioninLine = positioninLine;
    }

    public int getPositionInLine() {
        return positioninLine;
    }
}
