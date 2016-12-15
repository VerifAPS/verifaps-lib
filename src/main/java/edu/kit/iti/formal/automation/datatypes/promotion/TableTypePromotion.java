package edu.kit.iti.formal.automation.datatypes.promotion;

import edu.kit.iti.formal.automation.datatypes.Any;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 24.11.16.
 */
public class TableTypePromotion implements TypePromotion {
    private List<Any[]> table = new ArrayList<>();

    public TableTypePromotion() {
    }

    public TableTypePromotion(List<Any[]> table) {
        this.table = table;
    }

    public static TableTypePromotion getDefault() {
        TableTypePromotion t = new TableTypePromotion();
        return t;
    }

    @Override
    public Any getPromotion(Any a, Any b) {
        for (Any[] ary : table) {
            if (ary[0].equals(a) && ary[1].equals(b))
                return ary[2];
        }
        return null;
    }
}
