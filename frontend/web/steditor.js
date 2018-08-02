//http://codemirror.net/demo/simplemode.html

const REKEYWORDS = /(IF|ARRAY|CASE|AT|BY|CONSTANT|FOR|ELSIF|END_CASE|EXIT|F_EDGE|INTERVAL|NIL|NON_RETAIN|OF|ON|PRIORITY|READ_ONLY|READ_WRITE|RETAIN|RETURN|=>|R_EDGE|SINGLE|STRUCT|TASK|TO|WHILE|TYPE|UNTIL)\b/i;

const BUILT_DATATPYES = /(?:ANY|ANY_BIT|ANY_DATE|DT|DATE|ANY_DERIVED|ANY_ELEMENTARY|ANY_INT|ANY_NUM|ANY_REAL|ANY_STRING|BOOL|BYTE|DATE_AND_TIME|DINT|DWORD|INT|LINT|LREAL|LWORD|REAL|SINT|STRING|TIME|TIME_OF_DAY|TOD|UDINT|UINT|ULINT|USINT|WORD|WSTRING)/

const RE_ST_OPEN_BLOCK = /(VAR_OUTPUT|CONFIGURATION|FUNCTION|FUNCTION_BLOCK|REPEAT|STRUCT|RESOURCE|VAR|VAR_ACCESS|VAR_CONFIG|VAR_EXTERNAL|VAR_GLOBAL|VAR_INPUT|THEN|VAR_IN_OUT|VAR_TEMP|WITH|PROGRAM|DO)\b/;

const RE_ST_CLOSE_BLOCK = /(UNTIL|END_CASE|END_CONFIGURATION|END_FOR|END_FUNCTION|END_FUNCTION_BLOCK|END_IF|END_PROGRAM|END_REPEAT|END_RESOURCE|END_STRUCT|END_TYPE|END_VAR|END_WHILE)\b/;


import 'codemirror/addon/mode/simple';
import 'codemirror/lib/codemirror.css';
import 'codemirror/theme/monokai.css';
import CodeMirror from 'codemirror';

import $ from 'jquery';

function defineStMode() {
    CodeMirror.defineSimpleMode("st", {
        // The start state contains the rules that are intially used
        start: [
            // The regex matches the token, the token property contains the type
            {regex: /(WSTRING#)?"(?:[^\\]|\\.)*?(?:"|$)/, token: "string"},
            {regex: /(STRING#)?'(?:[^\\]|\\.)*?(?:'|$)/, token: "string"},

            {regex: /(TIME_OF_DAY|TOD)#\d{1,2}:\d{1,2}:\d{1,2}(\.[0-9]{,3})/, token: "atom"},
            {regex: /(DATE)#\d+-\d+-\d+/, token: "atom"},
            {regex: /(TIME|T)#((\d|[_])+(ms|s|m|h))*/, token: "atom"},
            {regex: /(DATE_AND_TIME|DT)#\d+-\d+-\d+-\d{1,2}:\d{1,2}:\d{1,2}(\.[0-9]{,3})/, token: "atom"},
            {regex: REKEYWORDS, token: "keyword"},
            {regex: RE_ST_OPEN_BLOCK, token: "keyword", indent: true},
            {regex: RE_ST_CLOSE_BLOCK, token: "keyword", dedent: true},

            {regex: /true|false|null/i, token: "atom"},
            {regex: /(U?[SLD]?INT#)?((1[06]|8|2)#)?[_\d]+/i, token: "number"},
            {regex: /(L?REAL#)?[\d_]+\.[\d_]+(e\d+)?/i, token: "number"},
            {regex: /\{.*?\}/, token: 'hint'},
            {regex: /\/\/.*/, token: "comment"},

            // A next property will cause the mode to move to a different state
            {regex: /\/\*/, token: "comment", next: "comment"},
            {regex: /\(\*/, token: "comment", next: "commentRound"},

            {regex: /[\w][\w\d]*/, token: "variable"},
        ],
        commentRound: [
            {regex: /.*?\*\)/, token: "comment", next: "start"},
            {regex: /.*/, token: "comment"}
        ],
        // The multi-line comment state.
        comment: [
            {regex: /.*?\*\//, token: "comment", next: "start"},
            {regex: /.*/, token: "comment"}
        ],
        // The meta property contains global information about the mode. It
        // can contain properties like lineComment, which are supported by
        // all modes, and also directives like dontIndentStates, which are
        // specific to simple modes.
        meta: {
            dontIndentStates: ["comment"],
            lineComment: "//"
        }
    });
}

export let stCodeEditor;
$(function () {
    defineStMode();
    stCodeEditor = CodeMirror(document.getElementById("editor"), {
        lineNumbers: true,
        gutter: ["gutter-errors", "gutter-warnings"],
        mode: "st"
    });
});

