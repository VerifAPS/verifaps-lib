INTERFACE ITF1
END_INTERFACE

INTERFACE ITF2
END_INTERFACE

INTERFACE ITF3
END_INTERFACE

CLASS ClBase IMPLEMENTS ITF1, ITF2
END_CLASS

CLASS ClDerived EXTENDS ClBase
END_CLASS

PROGRAM A
  VAR
    instbase : ClBase;
    instderived: ClDerived;
    rinstBase1, pinstBase2: REF_TO ClBase;
    rinstDerived1, rinstDerived2: REF_TO ClDerived;
    rinstDerived3, rinstDerived4: REF_TO ClDerived;
    interf1: ITF1;
    interf2: ITF2;
    interf3: ITF3;
  END_VAR

rinstBase1:= REF(instBase); // rinstbase1 references base class
rinstBase2:= REF(instDerived); // rinstbase2 references derived class

rinstDerived1 ?= rinstBase1; // rinstDerived1 == NULL
rinstDerived2 ?= rinstBase2; // rinstDerived2 will contain a valid
                             // reference to instDerived
interf1:= instbase;    // interf1 is a reference to base class
interf2:= instderived; // interf2 is a reference to derived class

rinstDerived3 ?= interf1; // rinstDerived3 == NULL
rinstDerived4 ?= interf2; // rinstDerived4 will contain a valid
                          // reference to instDerived

rinstBase1:= REF(instBase); // rinstbase1 references base class
rinstBase2:= REF(instDerived); // rinstbase2 references derived class

rinstBase1^.x := interf1^.func();  // 42
rinstBase2^.x := interf2^.func();  // 24

END_PROGRAM

