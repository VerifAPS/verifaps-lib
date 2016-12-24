package edu.kit.iti.formal.automation.testtables.model.options;

/*-
 * #%L
 * geteta
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

import java.beans.BeanInfo;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyDescriptor;
import java.lang.reflect.InvocationTargetException;
import java.util.Properties;

/**
 * Created on 16.12.16
 * @author Alexander Weigl
 * @version 2
 */
public class PropertyInitializer {

    private final Properties properties;
    private Object value;

    public PropertyInitializer(Object value, Properties properties) {
        this.value = value;
        this.properties = properties;
    }

    public static void initialize(Object value, Properties properties) {
        new PropertyInitializer(value, properties).inject("");
    }

    public void inject(String namespace) {
        try {
            BeanInfo info = Introspector.getBeanInfo(value.getClass());
            for (PropertyDescriptor prop : info.getPropertyDescriptors()) {
                Property p = prop.getReadMethod().getAnnotation(Property.class);
                if (p != null) {
                    String path = getPath(namespace, p, prop);
                    if (isSimpleType(prop.getPropertyType())) {
                        set(path, prop);
                    } else {
                        goDeeper(path, prop);
                    }
                }
            }
        } catch (IntrospectionException e) {
            e.printStackTrace();
        }
        try {
            InitializableFromProperties pi = (InitializableFromProperties) value;
            pi.initialize(namespace, properties);
        } catch (ClassCastException cce) {
        }
    }

    private String getPath(String namespace, Property p, PropertyDescriptor f) {
        if (p.value().isEmpty()) {
            return join(namespace, f.getName());
        } else {
            return join(namespace, p.value());
        }
    }

    private void goDeeper(String path, PropertyDescriptor f) {
        try {
            Object oldValue = value;
            value = f.getReadMethod().invoke(value);
            inject(path);
            value = oldValue;
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        } catch (InvocationTargetException e) {
            e.printStackTrace();
        }
    }

    private void set(String name, PropertyDescriptor f) {
        Class<?> type = f.getPropertyType();
        try {
            String val = getString(name);
            Object s = null;
            if (type.isEnum()) {
                for (Object o : type.getEnumConstants()) {
                    if (o.toString().equals(val))
                        s = o;
                }
            } else if (type == Integer.class)
                s = Integer.parseInt(val);
            else if (type == Boolean.class)
                s = val.equalsIgnoreCase("true");
            else if (type == String.class)
                s = val;
            else if (type == Long.class)
                s = Long.parseLong(val);

            f.getWriteMethod().invoke(value, s);
        } catch (NullPointerException npe) {
            //do nothing
        } catch (InvocationTargetException | IllegalAccessException e) {
            e.printStackTrace();
        }
    }

    private String getString(String name) {
        String val = properties.getProperty(name, null);
        if (val == null)
            throw new NullPointerException();
        return val;
    }

    private String join(String namespace, String name) {
        if (namespace == null || namespace.isEmpty())
            return name;
        return String.join(".", namespace, name);
    }

    private boolean isSimpleType(Class<?> type) {
        return type.isEnum() || type == Integer.class || type == Boolean.class || type == String.class || type == Long.class;
    }
}
