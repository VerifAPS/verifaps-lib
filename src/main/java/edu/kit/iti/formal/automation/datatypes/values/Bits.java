package edu.kit.iti.formal.automation.datatypes.values;

/**
 * Created by weigl on 11.06.14.
 * Immutable
 */
public class Bits {
    private long register;
    private final long nbits;

    public Bits(long nbits) {
        this(0, nbits);
    }

    public Bits(long register, long nbits) {
        this.nbits = nbits;
        this.register = register & allMask(); // trunc
    }

    private long allMask() {
        if (nbits == 64) {
            return -1L;
        } else {
            return (1L << nbits) - 1;
        }
    }

    public Bits shl(int n) {
        return new Bits(register << n, nbits);
    }

    public Bits shr(int n) {
        return new Bits(register >>> n, nbits);
    }


    public Bits rol(int n) {
        assert n <= nbits;

        if (n == nbits) {
            return this;
        }


        long maskAll = allMask();
        long maskRetain = (2 << (nbits - n)) - 1;
        long maskLoss = ~maskRetain & maskAll;

        long loss = register & maskRetain;
        long last = (loss >> (nbits - n));
        return new Bits((register << n) | last, nbits);
    }


    public Bits ror(int n) {
        long maskAll = allMask();
        long maskLoss = (2 << n) - 1;

        long loss = maskLoss & register;
        long first = loss << n;

        return new Bits((register >>> n) | first, nbits);
    }

    public long getRegister() {
        return register;
    }


    public Bits and(Bits other) {
        return new Bits(register & other.register, nbits);
    }

    public Bits or(Bits other) {
        return new Bits(register | other.register, nbits);
    }

    public Bits xor(Bits other) {
        return new Bits(register ^ other.register, nbits);
    }


    @Override
    public String toString() {
        return "Bits{" +
                "register=" + register +
                ", nbits=" + nbits +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Bits)) return false;

        Bits bits = (Bits) o;

        if (nbits != bits.nbits) return false;
        if (register != bits.register) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = (int) (register ^ (register >>> 32));
        result = 31 * result + (int) (nbits ^ (nbits >>> 32));
        return result;
    }

    public void setRegister(long register) {
        this.register = register;
    }
}
