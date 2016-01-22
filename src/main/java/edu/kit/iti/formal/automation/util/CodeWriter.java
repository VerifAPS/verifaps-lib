package edu.kit.iti.formal.automation.util;

import java.io.Serializable;

/**
 * @author weigla
 * @date 15.06.2014
 */
public class CodeWriter implements Serializable, CharSequence {
    protected StringBuilder sb = new StringBuilder();

    private boolean uppercaseKeywords = true;
    private String ident = "    ";
    private int identDepth = 0;


    public CodeWriter appendf(String fmt, Object... args){
        return append(String.format(fmt, args));
    }

    public CodeWriter appendIdent() {
        for (int i = 0; i < identDepth; i++) {
            sb.append(ident);
        }
        return this;
    }

    public CodeWriter increaseIndent() {
        identDepth++;
        return this;
    }

    public CodeWriter decreaseIndent() {
        identDepth--;
        return this;
    }

    public CodeWriter keyword(String keyword) {
    	return append(uppercaseKeywords?keyword.toUpperCase():keyword.toLowerCase());
    }
    
    public CodeWriter nl() {
        sb.append("\n");
        appendIdent();
        return this;
    }

    public CodeWriter append(Object obj) {
        sb.append(obj);
        return this;
    }

    public CodeWriter append(float f) {
        sb.append(f);
        return this;
    }

    public CodeWriter insert(int offset, boolean b) {
        sb.insert(offset, b);
        return this;
    }

    public int lastIndexOf(String str, int fromIndex) {
        return sb.lastIndexOf(str, fromIndex);
    }

    public char charAt(int index) {
        return sb.charAt(index);

    }

    public int codePointCount(int beginIndex, int endIndex) {
        return sb.codePointCount(beginIndex, endIndex);

    }

    public CodeWriter insert(int offset, char c) {
        sb.insert(offset, c);
        return this;
    }

    public CodeWriter append(double d) {
        sb.append(d);
        return this;
    }

    public CodeWriter insert(int dstOffset, CharSequence s) {
        sb.insert(dstOffset, s);
        return this;
    }

    public int offsetByCodePoints(int index, int codePointOffset) {
        return sb.offsetByCodePoints(index, codePointOffset);
    }

    public CodeWriter insert(int offset, long l) {
        sb.insert(offset, l);
        return this;
    }

    public CodeWriter insert(int offset, int i) {
        sb.insert(offset, i);
        return this;
    }

    public void setCharAt(int index, char ch) {
        sb.setCharAt(index, ch);

    }

    public int lastIndexOf(String str) {
        return sb.lastIndexOf(str);
    }

    public void ensureCapacity(int minimumCapacity) {
        sb.ensureCapacity(minimumCapacity);
    }

    public String substring(int start) {
        return sb.substring(start);

    }

    public CodeWriter append(char[] str) {
        sb.append(str);
        return this;
    }

    public int codePointAt(int index) {
        return sb.codePointAt(index);
    }

    public int indexOf(String str, int fromIndex) {
        return sb.indexOf(str, fromIndex);
    }

    public CodeWriter append(CharSequence s, int start, int end) {
        sb.append(s, start, end);
        return this;
    }

    public CodeWriter append(char[] str, int offset, int len) {
        sb.append(str, offset, len);
        return this;
    }

    public int codePointBefore(int index) {
        return sb.codePointBefore(index);
    }

    public CodeWriter insert(int offset, float f) {
        sb.insert(offset, f);
        return this;
    }

    public String substring(int start, int end) {
        return sb.substring(start, end);
    }

    public int length() {
        return sb.length();
    }

    public CodeWriter append(StringBuffer sb) {
        this.sb.append(sb);
        return this;
    }

    public CodeWriter reverse() {
        sb.reverse();
        return this;
    }

    public int indexOf(String str) {
        return sb.indexOf(str);
    }

    public CodeWriter insert(int offset, double d) {
        sb.insert(offset, d);
        return this;
    }

    public void trimToSize() {
        sb.trimToSize();
    }

    public void setLength(int newLength) {
        sb.setLength(newLength);
    }

    public int capacity() {
        return sb.capacity();
    }

    public CodeWriter insert(int offset, char[] str) {
        sb.insert(offset, str);
        return this;
    }

    public CodeWriter insert(int offset, String str) {
        sb.insert(offset, str);
        return this;
    }

    public CodeWriter appendCodePoint(int codePoint) {
        sb.appendCodePoint(codePoint);
        return this;
    }

    public CodeWriter append(char c) {
        sb.append(c);
        return this;
    }

    public CharSequence subSequence(int start, int end) {
        return sb.subSequence(start, end);
    }

    public CodeWriter delete(int start, int end) {
        sb.delete(start, end);
        return this;
    }

    public CodeWriter append(long lng) {
        sb.append(lng);
        return this;
    }

    public CodeWriter insert(int dstOffset, CharSequence s, int start, int end) {
        sb.insert(dstOffset, s, start, end);
        return this;
    }

    public CodeWriter insert(int index, char[] str, int offset, int len) {
        sb.insert(index, str, offset, len);
        return this;
    }

    public CodeWriter append(int i) {
        sb.append(i);
        return this;
    }

    public CodeWriter append(CharSequence s) {
        sb.append(s);
        return this;
    }

    public CodeWriter append(boolean b) {
        sb.append(b);
        return this;
    }

    public CodeWriter insert(int offset, Object obj) {
        sb.insert(offset, obj);
        return this;
    }

    public CodeWriter append(String str) {
        sb.append(str);
        return this;
    }

    public CodeWriter deleteCharAt(int index) {
        sb.deleteCharAt(index);
        return this;
    }

    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        sb.getChars(srcBegin, srcEnd, dst, dstBegin);
    }

    public CodeWriter replace(int start, int end, String str) {
        sb.replace(start, end, str);
        return this;
    }

    @Override
    public String toString() {
        return sb.toString();
    }

    public CodeWriter deleteLast() {
        return deleteLast(1);
    }
    

    public CodeWriter deleteLast(int i) {
        sb.setLength(sb.length() - i);
        return this;
    }



}