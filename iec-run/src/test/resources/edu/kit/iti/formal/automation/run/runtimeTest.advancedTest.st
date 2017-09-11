TYPE
    TrafficLight : (Red, Green);
END_TYPE

PROGRAM PedestrianTrafficLight

    VAR_INPUT
        pedBtnPress : BOOL := true;
    END_VAR

    VAR_OUTPUT
        carLight : TrafficLight;
        pedLight : TrafficLight;
        counter : INT := 50;
    END_VAR

    VAR
        buttonPressedBefore : BOOL := false;
    END_VAR


    IF (NOT buttonPressedBefore) AND pedBtnPress THEN
        carLight := TrafficLight#Red;
    END_IF

    IF counter = 10 THEN
        pedLight := TrafficLight#Green;
    ELSIF counter = 40 THEN
     pedLight := TrafficLight#Red;
    ELSIF counter = 50 THEN
        carLight := TrafficLight#Green;
    END_IF

    IF carLight = TrafficLight#Red THEN
        counter := counter + 1;
    ELSE
        counter := 0;
    END_IF

    buttonPressedBefore := pedBtnPress;


END_PROGRAM