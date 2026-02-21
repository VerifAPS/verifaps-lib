// non-formal
CAL C10(ABC, FALSE, A, OUT, B)
CAL CMD_TMR(ABC, T#300ms, OUT, ELAPSED)

//formal parameters
CAL C10(
  CU := ABC,
  R  := FALSE,
  PV := A,
  Q  => OUT,
  CV => B)

CAL CMD_TMR(
  IN := ABC,
  PT := T#300ms,
  Q
  => OUT,
  ET => ELAPSED,
  ENO => ERR)

LD    A
ADD   5
ST    C10.PV
LD    ABC
ST    C10.CU
CAL   C10
LD    C10.CV

LIMIT( // Funktionsname
  EN := COND,
  IN := B,
  MN := 1,
  MX := 5,
  ENO => TEMPL
  )
ST A

// unclear
LD 1
LIMIT B, 5
ST A
// setzt aktuelles Ergebnis
// und verwendet es als IN
// neues aktuelles Ergebnis

FB_INST.M1(
  // Methodenname
  EN := COND,
  IN := B,
  MN := 1,
  MX := 5,
  ENO => TEMPL
)
ST A

LD 1
// setzt aktuelles Ergebnis
FB_INST.M1 B, 5 // und verwendet es als IN
ST A
// neues aktuelles Ergebnis