FUNCTION_BLOCK Magazin
    VAR_INPUT  CraneDown : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneOnConveyor : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneOnMagazin : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneSucked : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneUp : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  MagazinGreenLamp : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  MagazinSlider : BOOL; END_VAR {*Orwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SliderMovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  StartButtonMagazin : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  StartCommandMagazin : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  WorkpieceReady : BOOL; END_VAR {*Irwxp*}
    VAR  _state : Magazin_states_t; END_VAR {*Lrwxp*}
    VAR  _transit : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnectMagazineStartCommand : BOOL; END_VAR {*Lrwxp*}
    
    CASE _state OF 
        Magazin_states_t#Green_Lamp:
            _transit := FALSE;
            MagazinGreenLamp := TRUE;
            interconnectMagazineStartCommand := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init;
            END_IF;
        
        Magazin_states_t#Init:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Start_Magazin;
            END_IF;
        
        Magazin_states_t#Interstep:
            _transit := FALSE;
            StartCommandMagazin := TRUE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Magazin_states_t#convey;
            END_IF;
        
        Magazin_states_t#Magazin_Init:
            _transit := FALSE;
            MagazinSlider := TRUE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init_2;
            END_IF;
        
        Magazin_states_t#Magazin_Init_2:
            _transit := FALSE;
            MagazinSlider := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#Slider_Move_Back:
            _transit := FALSE;
            IF ((SliderMovedOut = TRUE) AND (SliderNotMovedOut = FALSE)) THEN
                MagazinSlider := FALSE;
            END_IF;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step1;
            END_IF;
        
        Magazin_states_t#Start_Magazin:
            _transit := FALSE;
            MagazinSlider := FALSE;
            MagazinGreenLamp := FALSE;
            StartVar := FALSE;
            StartCommandMagazin := FALSE;
            IF (StartButtonMagazin = TRUE) THEN
                interconnectMagazineStartCommand := TRUE;
            END_IF;
            IF interconnectMagazineStartCommand THEN
                _transit := TRUE;
                _state := Magazin_states_t#Green_Lamp;
            END_IF;
        
        Magazin_states_t#Step0:
            _transit := FALSE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Magazin_states_t#Slider_Move_Back;
            END_IF;
        
        Magazin_states_t#Step1:
            _transit := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#convey:
            _transit := FALSE;
            IF SliderNotMovedOut THEN
                MagazinSlider := TRUE;
            END_IF;
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step0;
            END_IF;
        
            END_CASE;
END_FUNCTION_BLOCK

