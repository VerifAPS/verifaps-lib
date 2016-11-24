package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.datatypes.values.*;
import org.antlr.v4.runtime.Token;

import java.util.BitSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Created by weigl on 11.06.14.
 */
public class ValueFactory {
    public static ScalarValue<Int, Integer> makeInt(int value) {
        return new ScalarValue<>(AnyInt.INT, value);
    }

    public static ScalarValue<SInt, Integer> makeSInt(int value) {
        return new ScalarValue<>(AnyInt.SINT, value);
    }

    public static ScalarValue<DInt, Integer> makeLInt(int value) {
        return new ScalarValue<>(AnyInt.DINT, value);
    }

    public static ScalarValue<LInt, Integer> makeDInt(int value) {
        return new ScalarValue<>(AnyInt.LINT, value);
    }


    public static ScalarValue<Int, Integer> makeInt() {
        return new ScalarValue<>(AnyInt.INT, AnyInt.DEFAULT);
    }

    public static ScalarValue<SInt, Integer> makeSInt() {
        return new ScalarValue<>(AnyInt.SINT, AnyInt.DEFAULT);
    }

    public static ScalarValue<DInt, Integer> makeLInt() {
        return new ScalarValue<>(AnyInt.DINT, AnyInt.DEFAULT);
    }

    public static ScalarValue<LInt, Integer> makeDInt() {
        return new ScalarValue<>(AnyInt.LINT, AnyInt.DEFAULT);
    }


    public static <T extends AnyBit> ScalarValue<T, BitSet> makeAnyBit(T dataType) {
        return new ScalarValue<>(dataType, new BitSet(dataType.getBitLength()));
    }

    public static ScalarValue<AnyBit.Bool, BitSet> makeBool() {
        return makeAnyBit(AnyBit.BOOL);
    }

    public static ScalarValue<AnyBit.Word, BitSet> makeWord() {
        return makeAnyBit(AnyBit.WORD);
    }

    public static ScalarValue<AnyBit.DWord, BitSet> makeDWord() {
        return makeAnyBit(AnyBit.DWORD);
    }

    public static ScalarValue<AnyBit.LWord, BitSet> makeLWord() {
        return makeAnyBit(AnyBit.LWORD);
    }

    public static Expression parseLiteral(String text) {
        return null;
    }

    public static ScalarValue<? extends AnyBit, Bits> parseBitLiteral(Token s) {
        ScalarValue<? extends AnyBit, Bits> val = parseBitLiteral(s.getText());
        Utils.setPositionComplete(val, s);
        return val;
    }


    public static ScalarValue<? extends AnyBit, Bits> parseBitLiteral(String s) {
        String first = getPrefix(s);

        if ("TRUE".equalsIgnoreCase(s))
            return new ScalarValue<>(AnyBit.BOOL, new Bits(1l, AnyBit.BOOL.getBitLength()));
        if ("FALSE".equalsIgnoreCase(s))
            return new ScalarValue<>(AnyBit.BOOL, new Bits(0l, AnyBit.BOOL.getBitLength()));

        if (first != null) {
            long value = parseOrdinal(removePrefix(s));
            switch (first) {
                case "BYTE":
                    return new ScalarValue<>(AnyBit.BYTE, new Bits(value, AnyBit.BYTE.getBitLength()));
                case "LWORD":
                    return new ScalarValue<>(AnyBit.LWORD, new Bits(value, AnyBit.LWORD.getBitLength()));
                case "WORD":
                    return new ScalarValue<>(AnyBit.WORD, new Bits(value, AnyBit.WORD.getBitLength()));
                case "DWORD":
                    return new ScalarValue<>(AnyBit.DWORD, new Bits(value, AnyBit.DWORD.getBitLength()));
                case "BOOL":
                    return new ScalarValue<>(AnyBit.BOOL, new Bits(value, AnyBit.BOOL.getBitLength()));
                default:
                    throw new IllegalArgumentException();
            }
        } else {
            throw new IllegalArgumentException();
        }
    }

    public static ScalarValue<? extends AnyInt, Long> parseIntegerLiteral(Token token) {
        ScalarValue<? extends AnyInt, Long> val = parseIntegerLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<? extends AnyInt, Long> parseIntegerLiteral(String s) {
        String first = getPrefix(s);

        int bits = 0;
        long value = parseOrdinal(removePrefix(s));

        if (first == null || "INT".equalsIgnoreCase(first)) {
            return new ScalarValue<>(AnyInt.INT, value);
        } else {
            switch (first) {
                case "2":
                case "8":
                case "16":
                    value = parseOrdinal(s);
                    return new ScalarValue<>(AnyInt.INT, value);
                case "SINT":
                    return new ScalarValue<>(AnyInt.SINT, value);
                case "DINT":
                    return new ScalarValue<>(AnyInt.DINT, value);
                case "LINT":
                    return new ScalarValue<>(AnyInt.LINT, value);
                case "USINT":
                    return new ScalarValue<>(AnyInt.USINT, value);
                case "UINT":
                    return new ScalarValue<>(AnyInt.UINT, value);
                case "UDINT":
                    return new ScalarValue<>(AnyInt.UDINT, value);
                case "ULINT":
                    return new ScalarValue<>(AnyInt.ULINT, value);
            }
        }
        throw new IllegalStateException();
    }


    private static long parseOrdinal(String s) {
        String prefix = getPrefix(s);
        int radix = 10;
        if (prefix != null) {
            radix = Integer.parseInt(prefix);
        }
        try {
            return Long.parseLong(removePrefix(s), radix);
        } catch (NumberFormatException nfe) {
            return 0;
        }
    }

    public static ScalarValue<EnumerateType, String> makeEnumeratedValue(Token token) {
        ScalarValue<EnumerateType, String> val = makeEnumeratedValue(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<EnumerateType, String> makeEnumeratedValue(String s) {
        EnumerateType et = new EnumerateType(getPrefix(s));
        return new ScalarValue<>(et, removePrefix(s));
    }

    public static ScalarValue<? extends IECString, String> parseStringLiteral(Token token) {
        ScalarValue<? extends IECString, String> val = parseStringLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<? extends IECString, String> parseStringLiteral(String s) {
        String content = s.substring(1, s.length() - 1);
        if (s.startsWith("'"))
            return new ScalarValue<IECString.String, String>(IECString.STRING_8BIT, content);
        else
            return new ScalarValue<IECString.WString, String>(IECString.STRING_16BIT, content);
    }

    public static ScalarValue<TimeType, TimeValue> parseTimeLiteral(Token token) {
        ScalarValue<TimeType, TimeValue> val = parseTimeLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<TimeType, TimeValue> parseTimeLiteral(String s) {
        TimeValue tv = new TimeValue();
        s = removePrefix(s).replace("_", "");
        Pattern extractNumbers = Pattern.compile("([.0-9]+)([hmsd]{1,2})");
        Matcher matcher = extractNumbers.matcher(s);


        while (matcher.find()) {
            String num = matcher.group(1);
            String mod = matcher.group(2);

            double val = Double.parseDouble(num);

            switch (mod) {
                case "d":
                    tv.setDays(val);
                    break;

                case "h":
                    tv.setHours(val);
                    break;

                case "m":
                    tv.setMinutes(val);
                    break;

                case "s":
                    tv.setSeconds(val);
                    break;

                case "ms":
                    tv.setMillieseconds(val);
                    break;
            }
        }

        return new ScalarValue<>(TimeType.TIME_TYPE, tv);
    }

    private static String removePrefix(String s) {
        int beginIndex = s.indexOf('#');
        if (beginIndex == -1)
            return s;

        beginIndex += 1;
        return s.substring(beginIndex);
    }

    public static String getPrefix(String s) {
        int beginIndex = s.indexOf('#');
        if (beginIndex == -1)
            return null;
        return s.substring(0, beginIndex);
    }


    public static ScalarValue<AnyBit.Bool, Bits> makeBool(Token token) {
        ScalarValue<AnyBit.Bool, Bits> val = makeBool(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<AnyBit.Bool, Bits> makeBool(String text) {
        return new ScalarValue<AnyBit.Bool, Bits>(AnyBit.BOOL, new Bits(text.equals("TRUE") ? 1 : 0, 1));
    }

    public static ScalarValue<AnyBit.Bool, Boolean> makeBool(boolean val) {
        return new ScalarValue<AnyBit.Bool, Boolean>(AnyBit.BOOL, val);
    }

    public static ScalarValue<? extends AnyReal, Double> parseRealLiteral(Token token) {
        ScalarValue<? extends AnyReal, Double> val = parseRealLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<? extends AnyReal, Double> parseRealLiteral(String s) {
        s = removePrefix(s);
        double val = Double.parseDouble(s);
        return new ScalarValue<>(AnyReal.LREAL, val);
    }

    public static ScalarValue<AnyDate.DateAndTime, DateAndTimeValue> parseDateAndTimeLiteral(Token s) {
        ScalarValue<AnyDate.DateAndTime, DateAndTimeValue> val = parseDateAndTimeLiteral(s.getText());
        Utils.setPositionComplete(val, s);
        return val;
    }

    public static ScalarValue<AnyDate.DateAndTime, DateAndTimeValue> parseDateAndTimeLiteral(String s) {
        s = removePrefix(s);

        String a = s.substring(0, "yyyy-mm-dd".length());
        String b = s.substring("yyyy-mm-dd-".length());

        DateValue date = parseDateLiteral(a).getValue();
        TimeOfDayValue tod = parseTimeOfDayLiteral(b).getValue();
        DateAndTimeValue val = new DateAndTimeValue(date, tod);
        return new ScalarValue<>(AnyDate.DATE_AND_TIME, val);
    }

    public static ScalarValue<AnyDate.Date, DateValue> parseDateLiteral(Token token) {
        ScalarValue<AnyDate.Date, DateValue> val = parseDateLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<AnyDate.Date, DateValue> parseDateLiteral(String s) {
        Pattern pattern = Pattern.compile("(?<year>\\d\\d\\d\\d)-(?<month>\\d?\\d)-(?<day>\\d?\\d)");

        Matcher matcher = pattern.matcher(removePrefix(s));
        if (matcher.matches()) {
            int year = Integer.parseInt(matcher.group("year"));
            int month = Integer.parseInt(matcher.group("month"));
            int day = Integer.parseInt(matcher.group("day"));
            DateValue date = new DateValue(year, month, day);
            return new ScalarValue<>(AnyDate.DATE, date);
        } else {
            throw new IllegalArgumentException("given string is not a time of day value");
        }
    }

    public static ScalarValue<AnyDate.TimeOfDay, TimeOfDayValue> parseTimeOfDayLiteral(Token token) {
        ScalarValue<AnyDate.TimeOfDay, TimeOfDayValue> val = parseTimeOfDayLiteral(token.getText());
        Utils.setPositionComplete(val, token);
        return val;
    }

    public static ScalarValue<AnyDate.TimeOfDay, TimeOfDayValue> parseTimeOfDayLiteral(String s) {
        Pattern pattern = Pattern.compile("(?<hour>\\d?\\d):(?<min>\\d?\\d):(?<sec>\\d?\\d)(.(?<ms>\\d?\\d))?");

        Matcher matcher = pattern.matcher(removePrefix(s));
        if (matcher.matches()) {

            int hour = Integer.parseInt(matcher.group("hour"));
            int min = Integer.parseInt(matcher.group("min"));
            int sec = Integer.parseInt(matcher.group("sec"));

            int ms = 0;
            if (matcher.group("ms") != null)
                ms = Integer.parseInt(matcher.group("ms"));

            TimeOfDayValue tod = new TimeOfDayValue(hour, min, sec, ms);

            return new ScalarValue<>(AnyDate.TIME_OF_DAY, tod);

        } else {
            throw new IllegalArgumentException("given string is not a time of day value");
        }
    }


}