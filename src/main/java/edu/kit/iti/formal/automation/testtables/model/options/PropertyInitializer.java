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

import java.lang.reflect.Field;
import java.util.Properties;

/**
 * Created by weigl on 16.12.16.
 */
public class PropertyInitializer {

    private Object value;
    private final Properties properties;

    public PropertyInitializer(Object value, Properties properties) {
        this.value = value;
        this.properties = properties;
    }

    public void inject(String namespace) {
        Class<?> clazz = value.getClass();
        for (Field f : clazz.getFields()) {
            Property p = f.getAnnotation(Property.class);
            if (p != null) {
                String path = join(namespace, p.value());
                if (isSimpleType(f.getType())) {
                    set(path, f);
                } else {
                    goDeeper(path, f);
                }
            }
        }

        try {
            InitializableFromProperties pi = (InitializableFromProperties) value;
            pi.initialize(namespace, properties);
        } catch (ClassCastException cce) {
        }
    }

    private void goDeeper(String path, Field f) {
        try {
            Object oldValue = value;
            value = f.get(value);
            inject(path);
            value = oldValue;
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        }
    }

    private void set(String name, Field f) {
        try {
            String val = getString(name);


            if (f.getType().isEnum()) {
                for (Object s : f.getType().getEnumConstants()) {
                    if(s.toString().equals(val))
                        f.set(value, s);
                }
            }

            if (f.getType() == Integer.class)
                f.setInt(value, Integer.parseInt(val));
            if (f.getType() == Boolean.class)
                f.setBoolean(value, val.equalsIgnoreCase("true"));
            if (f.getType() == String.class)
                f.set(value, val);
            if (f.getType() == Long.class)
                f.set(value, Long.parseLong(val));
        } catch (NullPointerException npe) {
            //do nothing
        } catch (
                IllegalAccessException e)

        {
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
        return String.join(".", namespace, name);
    }


    private boolean isSimpleType(Class<?> type) {
        return type.isEnum() || type == Integer.class || type == Boolean.class || type == String.class || type == Long.class;
    }

    public static void initialize(Object value, Properties properties) {
        new PropertyInitializer(value, properties).inject("");
    }
}
