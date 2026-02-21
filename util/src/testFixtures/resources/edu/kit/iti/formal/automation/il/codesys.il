//https://help.codesys.com/api-content/2/codesys/3.5.12.0/en/_cds_f_programming_language_fbd_ld_il/
LD BVar1
ST inst.IN
JMPC mark1
CAL inst(
  PT:= t1,
  ET=> t2)
LD inst.Q
ST inst2.IN

mark1:
LD iVar2
ADD 230
