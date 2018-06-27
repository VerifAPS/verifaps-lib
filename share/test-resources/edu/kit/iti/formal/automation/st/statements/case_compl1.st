  CASE TW OF
            1,5 : anzeige := temperatur;
            2 : anzeige := umdrehung;
            4,6..10 : anzeige := status(tw-4);
            ELSE
            anzeige := 0;
            fehler := 1;
            END_CASE