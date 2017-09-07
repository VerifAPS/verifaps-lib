package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.Int

interface BiTypeVisitor<T> : DataTypeVisitor<T> {
    override fun visit(real: AnyReal): T

    override fun visit(real: AnyReal.Real): T

    override fun visit(real: AnyReal.LReal): T

    override fun visit(anyBit: AnyBit): T

    override fun visit(dateAndTime: AnyDate.DateAndTime): T


    override fun visit(timeOfDay: AnyDate.TimeOfDay): T


    override fun visit(date: AnyDate.Date): T


    override fun visit(anyInt: AnyInt): T {
        return visit(anyInt as AnyNum)
    }

    override fun visit(anyInt: AnySignedInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: AnyUnsignedInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: Int): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: SInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: DInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: LInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: UDInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: USInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: ULInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(anyInt: UInt): T {
        return visit(anyInt as AnyInt)
    }

    override fun visit(bool: AnyBit.Bool): T {
        return visit(bool as AnyBit)
    }

    override fun visit(word: AnyBit.Byte): T {
        return visit(word as AnyBit)
    }

    override fun visit(word: AnyBit.Word): T {
        return visit(word as AnyBit)
    }

    override fun visit(word: AnyBit.DWord): T {
        return visit(word as AnyBit)
    }

    override fun visit(word: AnyBit.LWord): T {
        return visit(word as AnyBit)
    }


    override fun visit(enumerateType: EnumerateType): T

    override fun visit(timeType: TimeType): T

    override fun visit(rangeType: RangeType): T

    override fun visit(recordType: RecordType): T


    override fun visit(pointerType: PointerType): T


    override fun visit(string: IECString.String): T


    override fun visit(wString: IECString.WString): T


    override fun visit(iecArray: IECArray): T

    override fun visit(anyNum: AnyNum): T

    override fun visit(classDataType: ClassDataType): T
}