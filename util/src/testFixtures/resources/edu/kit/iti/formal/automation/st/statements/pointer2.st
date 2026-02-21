(*--- pointer increment ---*)
udiAddress := ptByCurrDataOffs;
udiAddress := udiAddress + SIZEOF(ptByCurrDataOffs^);
ptByCurrDataOffs := udiAddress;
(* -- end of pointer increment ---*)

