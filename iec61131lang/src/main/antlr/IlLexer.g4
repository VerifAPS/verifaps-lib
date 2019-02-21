lexer grammar IlLexer;
import IEC61131Lexer;

//Overwrite
EOL: '\n'+;

WS
:
	[ \r\t]+ -> channel ( HIDDEN )
;
