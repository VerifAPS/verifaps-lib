oscat_examples = [
    {
        "name": "Simple On-Off Control",
        "steps": [
            {"name": "Init", "function": "output := 0"},
            {"name": "Check", "function": ""},
            {"name": "On", "function": "output := 1"},
            {"name": "Off", "function": "output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "On", "guard": "input > threshold"},
            {"src": "Check", "tgt": "Off", "guard": "input <= threshold"},
            {"src": "On", "tgt": "End", "guard": "True"},
            {"src": "Off", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "threshold", "output", "init"]
    },
    {
        "name": "Hysteresis Switch",
        "steps": [
            {"name": "Init", "function": "output := 0"},
            {"name": "Check", "function": ""},
            {"name": "On", "function": "output := 1"},
            {"name": "Off", "function": "output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "On", "guard": "input > on_threshold"},
            {"src": "Check", "tgt": "Off", "guard": "input < off_threshold"},
            {"src": "On", "tgt": "Check", "guard": "True"},
            {"src": "Off", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "False"}
        ],
        "variables": ["input", "on_threshold", "off_threshold", "output", "init"]
    },
    {
        "name": "Toggle by Rising Edge (T Flip-Flop)",
        "steps": [
            {"name": "Init", "function": "output := 0; last := 0"},
            {"name": "Check", "function": ""},
            {"name": "Toggle", "function": "output := 1 - output"},
            {"name": "End", "function": "last := input"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Toggle", "guard": "input == 1 and last == 0"},
            {"src": "Toggle", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 0 or last == 1"}
        ],
        "variables": ["input", "output", "last", "init"]
    },
    {
        "name": "Delay On Timer",
        "steps": [
            {"name": "Init", "function": "timer := 0; output := 0"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "timer := timer + 1"},
            {"name": "On", "function": "output := 1"},
            {"name": "Reset", "function": "timer := 0; output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and timer < delay"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "On", "guard": "input == 1 and timer >= delay"},
            {"src": "On", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "input == 0"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "timer", "delay", "output", "init"]
    },
    {
        "name": "Delay Off Timer",
        "steps": [
            {"name": "Init", "function": "timer := 0; output := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "output := 1"},
            {"name": "Count", "function": "timer := timer + 1"},
            {"name": "Reset", "function": "timer := 0; output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "input == 1"},
            {"src": "Set", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Count", "guard": "input == 0 and timer < delay"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "input == 0 and timer >= delay"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "timer", "delay", "output", "init"]
    },
    {
        "name": "Rising Edge Detection",
        "steps": [
            {"name": "Init", "function": "last := 0; edge := 0"},
            {"name": "Check", "function": ""},
            {"name": "Detect", "function": "edge := 1"},
            {"name": "End", "function": "last := input; edge := 0"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Detect", "guard": "input == 1 and last == 0"},
            {"src": "Detect", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 0 or last == 1"}
        ],
        "variables": ["input", "last", "edge", "init"]
    },
    {
        "name": "Falling Edge Detection",
        "steps": [
            {"name": "Init", "function": "last := 1; edge := 0"},
            {"name": "Check", "function": ""},
            {"name": "Detect", "function": "edge := 1"},
            {"name": "End", "function": "last := input; edge := 0"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Detect", "guard": "input == 0 and last == 1"},
            {"src": "Detect", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 1 or last == 0"}
        ],
        "variables": ["input", "last", "edge", "init"]
    },
    {
        "name": "Pulse Generator (fixed width)",
        "steps": [
            {"name": "Init", "function": "timer := 0; pulse := 0"},
            {"name": "Check", "function": ""},
            {"name": "StartPulse", "function": "pulse := 1; timer := 1"},
            {"name": "Pulse", "function": "timer := timer + 1"},
            {"name": "StopPulse", "function": "pulse := 0; timer := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "StartPulse", "guard": "trigger == 1"},
            {"src": "StartPulse", "tgt": "Pulse", "guard": "True"},
            {"src": "Pulse", "tgt": "Pulse", "guard": "timer < width"},
            {"src": "Pulse", "tgt": "StopPulse", "guard": "timer >= width"},
            {"src": "StopPulse", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["trigger", "timer", "width", "pulse", "init"]
    },
    {
        "name": "Up Counter",
        "steps": [
            {"name": "Init", "function": "cnt := 0"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "cnt := cnt + 1"},
            {"name": "Reset", "function": "cnt := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and cnt < max"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "reset", "cnt", "max", "init"]
    },
    {
        "name": "Down Counter",
        "steps": [
            {"name": "Init", "function": "cnt := max"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "cnt := cnt - 1"},
            {"name": "Reset", "function": "cnt := max"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and cnt > 0"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "reset", "cnt", "max", "init"]
    },
    {
        "name": "Comparator Greater",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a > b"},
            {"src": "Check", "tgt": "Reset", "guard": "a <= b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Comparator Less",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a < b"},
            {"src": "Check", "tgt": "Reset", "guard": "a >= b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Comparator Equal",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a == b"},
            {"src": "Check", "tgt": "Reset", "guard": "a != b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Comparator Not Equal",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a != b"},
            {"src": "Check", "tgt": "Reset", "guard": "a == b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Limit Upper Bound",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Clamp", "function": "out := upper"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Clamp", "guard": "input > upper"},
            {"src": "Check", "tgt": "End", "guard": "input <= upper"},
            {"src": "Clamp", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "upper", "out", "init"]
    },
    {
        "name": "Limit Lower Bound",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Clamp", "function": "out := lower"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Clamp", "guard": "input < lower"},
            {"src": "Check", "tgt": "End", "guard": "input >= lower"},
            {"src": "Clamp", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "lower", "out", "init"]
    },
    {
        "name": "Range Check",
        "steps": [
            {"name": "Init", "function": "in_range := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "in_range := 1"},
            {"name": "Reset", "function": "in_range := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "input >= low and input <= high"},
            {"src": "Check", "tgt": "Reset", "guard": "input < low or input > high"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "low", "high", "in_range", "init"]
    },
    {
        "name": "Rate Limiter (Ramp)",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "out := out + rate"},
            {"name": "Dec", "function": "out := out - rate"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "out < input"},
            {"src": "Check", "tgt": "Dec", "guard": "out > input"},
            {"src": "Check", "tgt": "End", "guard": "out == input"},
            {"src": "Inc", "tgt": "Check", "guard": "True"},
            {"src": "Dec", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "out", "rate", "init"]
    },
    {
        "name": "Deadband",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Pass", "function": "out := input"},
            {"name": "Block", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Pass", "guard": "input > upper or input < lower"},
            {"src": "Check", "tgt": "Block", "guard": "input <= upper and input >= lower"},
            {"src": "Pass", "tgt": "End", "guard": "True"},
            {"src": "Block", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "upper", "lower", "out", "init"]
    },
    {
        "name": "Absolute Value",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Negate", "function": "out := -input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Negate", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input >= 0"},
            {"src": "Negate", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "out", "init"]
    },
    {
        "name": "Integrator",
        "steps": [
            {"name": "Init", "function": "sum := 0"},
            {"name": "Check", "function": ""},
            {"name": "Add", "function": "sum := sum + input"},
            {"name": "Reset", "function": "sum := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Add", "guard": "enable == 1"},
            {"src": "Add", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "enable", "reset", "sum", "init"]
    },
    {
        "name": "Sample and Hold",
        "steps": [
            {"name": "Init", "function": "hold := 0"},
            {"name": "Check", "function": ""},
            {"name": "Sample", "function": "hold := input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Sample", "guard": "sample == 1"},
            {"src": "Check", "tgt": "End", "guard": "sample == 0"},
            {"src": "Sample", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "sample", "hold", "init"]
    },
    {
        "name": "S-R Latch",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "q := 1"},
            {"name": "Reset", "function": "q := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "s == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "r == 1"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["s", "r", "q", "init"]
    },
    {
        "name": "D Latch",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Latch", "function": "q := d"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Latch", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Latch", "tgt": "End", "guard": "True"}
        ],
        "variables": ["d", "enable", "q", "init"]
    },
    {
        "name": "Up-Down Counter",
        "steps": [
            {"name": "Init", "function": "cnt := 0"},
            {"name": "Check", "function": ""},
            {"name": "Up", "function": "cnt := cnt + 1"},
            {"name": "Down", "function": "cnt := cnt - 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Up", "guard": "up == 1"},
            {"src": "Check", "tgt": "Down", "guard": "down == 1"},
            {"src": "Check", "tgt": "End", "guard": "up == 0 and down == 0"},
            {"src": "Up", "tgt": "End", "guard": "True"},
            {"src": "Down", "tgt": "End", "guard": "True"}
        ],
        "variables": ["up", "down", "cnt", "init"]
    },
    {
        "name": "Multiplexer (2-input)",
        "steps": [
            {"name": "Init", "function": "out := a"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b"},
            {"name": "SetA", "function": "out := a"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "sel == 1"},
            {"src": "Check", "tgt": "SetA", "guard": "sel == 0"},
            {"src": "SetB", "tgt": "End", "guard": "True"},
            {"src": "SetA", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "sel", "out", "init"]
    },
    {
        "name": "Minimum Selector",
        "steps": [
            {"name": "Init", "function": "out := a"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "b < a"},
            {"src": "Check", "tgt": "End", "guard": "a <= b"},
            {"src": "SetB", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Maximum Selector",
        "steps": [
            {"name": "Init", "function": "out := a"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "b > a"},
            {"src": "Check", "tgt": "End", "guard": "a >= b"},
            {"src": "SetB", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Simple Arithmetic (a+b-c)",
        "steps": [
            {"name": "Init", "function": "out := a + b - c"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "End", "guard": "init"}
        ],
        "variables": ["a", "b", "c", "out", "init"]
    },
    {
        "name": "Signum",
        "steps": [
            {"name": "Init", "function": "sgn := 0"},
            {"name": "Check", "function": ""},
            {"name": "SetPos", "function": "sgn := 1"},
            {"name": "SetNeg", "function": "sgn := -1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetPos", "guard": "input > 0"},
            {"src": "Check", "tgt": "SetNeg", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input == 0"},
            {"src": "SetPos", "tgt": "End", "guard": "True"},
            {"src": "SetNeg", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "sgn", "init"]
    },
    {
        "name": "Increment If",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := count + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Inc", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "count", "init"]
    },
    {
        "name": "Decrement If",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Dec", "function": "count := count - 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Dec", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Dec", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "count", "init"]
    },
    {
        "name": "Clamp in Range",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "ClampLow", "function": "out := low"},
            {"name": "ClampHigh", "function": "out := high"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "ClampLow", "guard": "input < low"},
            {"src": "Check", "tgt": "ClampHigh", "guard": "input > high"},
            {"src": "Check", "tgt": "End", "guard": "input >= low and input <= high"},
            {"src": "ClampLow", "tgt": "End", "guard": "True"},
            {"src": "ClampHigh", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "low", "high", "out", "init"]
    },
    {
        "name": "Invert",
        "steps": [
            {"name": "Init", "function": "out := -input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "End", "guard": "init"}
        ],
        "variables": ["input", "out", "init"]
    },
    {
        "name": "Resettable Counter",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := count + 1"},
            {"name": "Reset", "function": "count := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "enable == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Inc", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["enable", "reset", "count", "init"]
    },
    {
        "name": "Modulo Counter",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := (count + 1) % mod"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Inc", "tgt": "End", "guard": "True"}
        ],
        "variables": ["enable", "mod", "count", "init"]
    },
    {
        "name": "Comparator GE (>=)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a >= b"},
            {"src": "Check", "tgt": "Reset", "guard": "a < b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Comparator LE (<=)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := 1"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a <= b"},
            {"src": "Check", "tgt": "Reset", "guard": "a > b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    {
        "name": "Set-Reset Flip-Flop (priority to set)",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "q := 1"},
            {"name": "Reset", "function": "q := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "set == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1 and set == 0"},
            {"src": "Check", "tgt": "End", "guard": "set == 0 and reset == 0"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["set", "reset", "q", "init"]
    },
    {
        "name": "Hold Last Value",
        "steps": [
            {"name": "Init", "function": "hold := 0"},
            {"name": "Check", "function": ""},
            {"name": "Hold", "function": "hold := input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Hold", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Hold", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "enable", "hold", "init"]
    },
    {
        "name": "Latch Until Reset",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Latch", "function": "q := 1"},
            {"name": "Reset", "function": "q := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Latch", "guard": "set == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Check", "tgt": "End", "guard": "set == 0 and reset == 0"},
            {"src": "Latch", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["set", "reset", "q", "init"]
    },
    {
        "name": "Minimum of three",
        "steps": [
            {"name": "Init", "function": "min1 := a if a < b else b"},
            {"name": "Check", "function": ""},
            {"name": "Min2", "function": "min2 := min1 if min1 < c else c"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Min2", "guard": "True"},
            {"src": "Min2", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "c", "min1", "min2", "init"]
    },
    {
        "name": "Maximum of three",
        "steps": [
            {"name": "Init", "function": "max1 := a if a > b else b"},
            {"name": "Check", "function": ""},
            {"name": "Max2", "function": "max2 := max1 if max1 > c else c"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Max2", "guard": "True"},
            {"src": "Max2", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "c", "max1", "max2", "init"]
    },
    {
        "name": "Set value if condition",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := val"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Set", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "val", "out", "init"]
    },
    {
        "name": "Reset to default if condition",
        "steps": [
            {"name": "Init", "function": "out := val"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := defval"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "val", "defval", "out", "init"]
    },
    {
        "name": "Sign Flip If Condition",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Flip", "function": "out := -input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Flip", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Flip", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "cond", "out", "init"]
    },
    {
        "name": "Reset If Negative",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input >= 0"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "out", "init"]
    },
    {
        "name": "Set to Max if Exceeds",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "SetMax", "function": "out := maxval"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetMax", "guard": "input > maxval"},
            {"src": "Check", "tgt": "End", "guard": "input <= maxval"},
            {"src": "SetMax", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "maxval", "out", "init"]
    },
    {
        "name": "Set to Min if Below",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "SetMin", "function": "out := minval"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetMin", "guard": "input < minval"},
            {"src": "Check", "tgt": "End", "guard": "input >= minval"},
            {"src": "SetMin", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "minval", "out", "init"]
    },
    {
        "name": "Reset If Out Of Bounds",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "input < minval or input > maxval"},
            {"src": "Check", "tgt": "End", "guard": "input >= minval and input <= maxval"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "minval", "maxval", "out", "init"]
    }
]

oscat_examples_upgraded = [
    # 1. Simple On-Off Control
    {
        "name": "Simple On-Off Control (Upgraded)",
        "steps": [
            {"name": "Init", "function": "output := 0"},
            {"name": "Check", "function": ""},
            {"name": "On", "function": "output := (input - threshold) * gain"},
            {"name": "Off", "function": "output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "On", "guard": "input > threshold"},
            {"src": "Check", "tgt": "Off", "guard": "input <= threshold"},
            {"src": "On", "tgt": "End", "guard": "True"},
            {"src": "Off", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "threshold", "gain", "output", "init"]
    },
    # 2. Hysteresis Switch
    {
        "name": "Hysteresis Switch (Upgraded)",
        "steps": [
            {"name": "Init", "function": "output := 0"},
            {"name": "Check", "function": ""},
            {"name": "On", "function": "output := input * scale"},
            {"name": "Off", "function": "output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "On", "guard": "input > on_threshold"},
            {"src": "Check", "tgt": "Off", "guard": "input < off_threshold"},
            {"src": "On", "tgt": "Check", "guard": "True"},
            {"src": "Off", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "False"}
        ],
        "variables": ["input", "on_threshold", "off_threshold", "scale", "output", "init"]
    },
    # 3. Toggle by Rising Edge (T Flip-Flop)
    {
        "name": "Toggle by Rising Edge (T Flip-Flop) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "output := 0; last := 0; toggle_count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Toggle", "function": "output := 1 - output; toggle_count := toggle_count + 1"},
            {"name": "End", "function": "last := input"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Toggle", "guard": "input == 1 and last == 0"},
            {"src": "Toggle", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 0 or last == 1"}
        ],
        "variables": ["input", "output", "last", "toggle_count", "init"]
    },
    # 4. Delay On Timer
    {
        "name": "Delay On Timer (Upgraded)",
        "steps": [
            {"name": "Init", "function": "timer := 0; output := 0"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "timer := timer + step"},
            {"name": "On", "function": "output := timer * scale"},
            {"name": "Reset", "function": "timer := 0; output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and timer < delay"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "On", "guard": "input == 1 and timer >= delay"},
            {"src": "On", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "input == 0"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "timer", "delay", "step", "scale", "output", "init"]
    },
    # 5. Delay Off Timer
    {
        "name": "Delay Off Timer (Upgraded)",
        "steps": [
            {"name": "Init", "function": "timer := 0; output := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "output := timer + 1"},
            {"name": "Count", "function": "timer := timer + 2"},
            {"name": "Reset", "function": "timer := 0; output := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "input == 1"},
            {"src": "Set", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Count", "guard": "input == 0 and timer < delay"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "input == 0 and timer >= delay"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "timer", "delay", "output", "init"]
    },
    # 6. Rising Edge Detection
    {
        "name": "Rising Edge Detection (Upgraded)",
        "steps": [
            {"name": "Init", "function": "last := 0; edge := 0; edge_count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Detect", "function": "edge := 1; edge_count := edge_count + 1"},
            {"name": "End", "function": "last := input; edge := 0"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Detect", "guard": "input == 1 and last == 0"},
            {"src": "Detect", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 0 or last == 1"}
        ],
        "variables": ["input", "last", "edge", "edge_count", "init"]
    },
    # 7. Falling Edge Detection
    {
        "name": "Falling Edge Detection (Upgraded)",
        "steps": [
            {"name": "Init", "function": "last := 1; edge := 0; edge_count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Detect", "function": "edge := 1; edge_count := edge_count + 1"},
            {"name": "End", "function": "last := input; edge := 0"}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Detect", "guard": "input == 0 and last == 1"},
            {"src": "Detect", "tgt": "End", "guard": "True"},
            {"src": "Check", "tgt": "End", "guard": "input == 1 or last == 0"}
        ],
        "variables": ["input", "last", "edge", "edge_count", "init"]
    },
    # 8. Pulse Generator (fixed width)
    {
        "name": "Pulse Generator (fixed width) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "timer := 0; pulse := 0"},
            {"name": "Check", "function": ""},
            {"name": "StartPulse", "function": "pulse := 1; timer := 1"},
            {"name": "Pulse", "function": "timer := timer * 2"},
            {"name": "StopPulse", "function": "pulse := 0; timer := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "StartPulse", "guard": "trigger == 1"},
            {"src": "StartPulse", "tgt": "Pulse", "guard": "True"},
            {"src": "Pulse", "tgt": "Pulse", "guard": "timer < width"},
            {"src": "Pulse", "tgt": "StopPulse", "guard": "timer >= width"},
            {"src": "StopPulse", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["trigger", "timer", "width", "pulse", "init"]
    },
    # 9. Up Counter
    {
        "name": "Up Counter (Upgraded)",
        "steps": [
            {"name": "Init", "function": "cnt := 0"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "cnt := cnt + 2"},
            {"name": "Reset", "function": "cnt := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and cnt < max"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "reset", "cnt", "max", "init"]
    },
    # 10. Down Counter
    {
        "name": "Down Counter (Upgraded)",
        "steps": [
            {"name": "Init", "function": "cnt := max"},
            {"name": "Check", "function": ""},
            {"name": "Count", "function": "cnt := cnt - 2"},
            {"name": "Reset", "function": "cnt := max"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Count", "guard": "input == 1 and cnt > 0"},
            {"src": "Count", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "reset", "cnt", "max", "init"]
    },
    # 11. Comparator Greater
    {
        "name": "Comparator Greater (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := a - b"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a > b"},
            {"src": "Check", "tgt": "Reset", "guard": "a <= b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 12. Comparator Less
    {
        "name": "Comparator Less (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := b - a"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a < b"},
            {"src": "Check", "tgt": "Reset", "guard": "a >= b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 13. Comparator Equal
    {
        "name": "Comparator Equal (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := a + b"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a == b"},
            {"src": "Check", "tgt": "Reset", "guard": "a != b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 14. Comparator Not Equal
    {
        "name": "Comparator Not Equal (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := abs(a - b)"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a != b"},
            {"src": "Check", "tgt": "Reset", "guard": "a == b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 15. Limit Upper Bound
    {
        "name": "Limit Upper Bound (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input + upper"},
            {"name": "Check", "function": ""},
            {"name": "Clamp", "function": "out := upper"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Clamp", "guard": "input > upper"},
            {"src": "Check", "tgt": "End", "guard": "input <= upper"},
            {"src": "Clamp", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "upper", "out", "init"]
    },
    # 16. Limit Lower Bound
    {
        "name": "Limit Lower Bound (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input - lower"},
            {"name": "Check", "function": ""},
            {"name": "Clamp", "function": "out := lower"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Clamp", "guard": "input < lower"},
            {"src": "Check", "tgt": "End", "guard": "input >= lower"},
            {"src": "Clamp", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "lower", "out", "init"]
    },
    # 17. Range Check
    {
        "name": "Range Check (Upgraded)",
        "steps": [
            {"name": "Init", "function": "in_range := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "in_range := input * 2"},
            {"name": "Reset", "function": "in_range := input // 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "input >= low and input <= high"},
            {"src": "Check", "tgt": "Reset", "guard": "input < low or input > high"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "low", "high", "in_range", "init"]
    },
    # 18. Rate Limiter (Ramp)
    {
        "name": "Rate Limiter (Ramp) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "out := out + 2*rate"},
            {"name": "Dec", "function": "out := out - 2*rate"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "out < input"},
            {"src": "Check", "tgt": "Dec", "guard": "out > input"},
            {"src": "Check", "tgt": "End", "guard": "out == input"},
            {"src": "Inc", "tgt": "Check", "guard": "True"},
            {"src": "Dec", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "out", "rate", "init"]
    },
    # 19. Deadband
    {
        "name": "Deadband (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Pass", "function": "out := input * 2"},
            {"name": "Block", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Pass", "guard": "input > upper or input < lower"},
            {"src": "Check", "tgt": "Block", "guard": "input <= upper and input >= lower"},
            {"src": "Pass", "tgt": "End", "guard": "True"},
            {"src": "Block", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "upper", "lower", "out", "init"]
    },
    # 20. Absolute Value
    {
        "name": "Absolute Value (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := abs(input)"},
            {"name": "Check", "function": ""},
            {"name": "Negate", "function": "out := -input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Negate", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input >= 0"},
            {"src": "Negate", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "out", "init"]
    },

    # 21. Integrator
    {
        "name": "Integrator (Upgraded)",
        "steps": [
            {"name": "Init", "function": "sum := 0"},
            {"name": "Check", "function": ""},
            {"name": "Add", "function": "sum := sum + input * 2"},
            {"name": "Reset", "function": "sum := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Add", "guard": "enable == 1"},
            {"src": "Add", "tgt": "Check", "guard": "True"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Reset", "tgt": "Check", "guard": "True"}
        ],
        "variables": ["input", "enable", "reset", "sum", "init"]
    },
    # 22. Sample and Hold
    {
        "name": "Sample and Hold (Upgraded)",
        "steps": [
            {"name": "Init", "function": "hold := 0"},
            {"name": "Check", "function": ""},
            {"name": "Sample", "function": "hold := input + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Sample", "guard": "sample == 1"},
            {"src": "Check", "tgt": "End", "guard": "sample == 0"},
            {"src": "Sample", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "sample", "hold", "init"]
    },
    # 23. S-R Latch
    {
        "name": "S-R Latch (Upgraded)",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "q := 1"},
            {"name": "Reset", "function": "q := -1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "s == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "r == 1"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["s", "r", "q", "init"]
    },
    # 24. D Latch
    {
        "name": "D Latch (Upgraded)",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Latch", "function": "q := d + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Latch", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Latch", "tgt": "End", "guard": "True"}
        ],
        "variables": ["d", "enable", "q", "init"]
    },
    # 25. Up-Down Counter
    {
        "name": "Up-Down Counter (Upgraded)",
        "steps": [
            {"name": "Init", "function": "cnt := 0"},
            {"name": "Check", "function": ""},
            {"name": "Up", "function": "cnt := cnt + 2"},
            {"name": "Down", "function": "cnt := cnt - 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Up", "guard": "up == 1"},
            {"src": "Check", "tgt": "Down", "guard": "down == 1"},
            {"src": "Check", "tgt": "End", "guard": "up == 0 and down == 0"},
            {"src": "Up", "tgt": "End", "guard": "True"},
            {"src": "Down", "tgt": "End", "guard": "True"}
        ],
        "variables": ["up", "down", "cnt", "init"]
    },
    # 26. Multiplexer (2-input)
    {
        "name": "Multiplexer (2-input) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := a + 1"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b + 1"},
            {"name": "SetA", "function": "out := a + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "sel == 1"},
            {"src": "Check", "tgt": "SetA", "guard": "sel == 0"},
            {"src": "SetB", "tgt": "End", "guard": "True"},
            {"src": "SetA", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "sel", "out", "init"]
    },
    # 27. Minimum Selector
    {
        "name": "Minimum Selector (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := a - b"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b - a"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "b < a"},
            {"src": "Check", "tgt": "End", "guard": "a <= b"},
            {"src": "SetB", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 28. Maximum Selector
    {
        "name": "Maximum Selector (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := a * 2"},
            {"name": "Check", "function": ""},
            {"name": "SetB", "function": "out := b * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetB", "guard": "b > a"},
            {"src": "Check", "tgt": "End", "guard": "a >= b"},
            {"src": "SetB", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 29. Simple Arithmetic (a+b-c)
    {
        "name": "Simple Arithmetic (a+b-c) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := a + b - c + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "End", "guard": "init"}
        ],
        "variables": ["a", "b", "c", "out", "init"]
    },
    # 30. Signum
    {
        "name": "Signum (Upgraded)",
        "steps": [
            {"name": "Init", "function": "sgn := 0"},
            {"name": "Check", "function": ""},
            {"name": "SetPos", "function": "sgn := input"},
            {"name": "SetNeg", "function": "sgn := -input"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetPos", "guard": "input > 0"},
            {"src": "Check", "tgt": "SetNeg", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input == 0"},
            {"src": "SetPos", "tgt": "End", "guard": "True"},
            {"src": "SetNeg", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "sgn", "init"]
    },
    # 31. Increment If
    {
        "name": "Increment If (Upgraded)",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := count + 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Inc", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "count", "init"]
    },
    # 32. Decrement If
    {
        "name": "Decrement If (Upgraded)",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Dec", "function": "count := count - 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Dec", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Dec", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "count", "init"]
    },
    # 33. Clamp in Range
    {
        "name": "Clamp in Range (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input * 2"},
            {"name": "Check", "function": ""},
            {"name": "ClampLow", "function": "out := low"},
            {"name": "ClampHigh", "function": "out := high"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "ClampLow", "guard": "input < low"},
            {"src": "Check", "tgt": "ClampHigh", "guard": "input > high"},
            {"src": "Check", "tgt": "End", "guard": "input >= low and input <= high"},
            {"src": "ClampLow", "tgt": "End", "guard": "True"},
            {"src": "ClampHigh", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "low", "high", "out", "init"]
    },
    # 34. Invert
    {
        "name": "Invert (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := -input * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "End", "guard": "init"}
        ],
        "variables": ["input", "out", "init"]
    },
    # 35. Resettable Counter
    {
        "name": "Resettable Counter (Upgraded)",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := count + 3"},
            {"name": "Reset", "function": "count := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "enable == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Inc", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["enable", "reset", "count", "init"]
    },
    # 36. Modulo Counter
    {
        "name": "Modulo Counter (Upgraded)",
        "steps": [
            {"name": "Init", "function": "count := 0"},
            {"name": "Check", "function": ""},
            {"name": "Inc", "function": "count := (count + 2) % mod"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Inc", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Inc", "tgt": "End", "guard": "True"}
        ],
        "variables": ["enable", "mod", "count", "init"]
    },
    # 37. Comparator GE (>=)
    {
        "name": "Comparator GE (>=) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := a + b"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a >= b"},
            {"src": "Check", "tgt": "Reset", "guard": "a < b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 38. Comparator LE (<=)
    {
        "name": "Comparator LE (<=) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := a * b"},
            {"name": "Reset", "function": "out := 0"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "a <= b"},
            {"src": "Check", "tgt": "Reset", "guard": "a > b"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "out", "init"]
    },
    # 39. Set-Reset Flip-Flop (priority to set)
    {
        "name": "Set-Reset Flip-Flop (priority to set) (Upgraded)",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "q := set + 1"},
            {"name": "Reset", "function": "q := reset - 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "set == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1 and set == 0"},
            {"src": "Check", "tgt": "End", "guard": "set == 0 and reset == 0"},
            {"src": "Set", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["set", "reset", "q", "init"]
    },
    # 40. Hold Last Value
    {
        "name": "Hold Last Value (Upgraded)",
        "steps": [
            {"name": "Init", "function": "hold := 0"},
            {"name": "Check", "function": ""},
            {"name": "Hold", "function": "hold := input + 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Hold", "guard": "enable == 1"},
            {"src": "Check", "tgt": "End", "guard": "enable == 0"},
            {"src": "Hold", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "enable", "hold", "init"]
    },
    # 41. Latch Until Reset
    {
        "name": "Latch Until Reset (Upgraded)",
        "steps": [
            {"name": "Init", "function": "q := 0"},
            {"name": "Check", "function": ""},
            {"name": "Latch", "function": "q := set * 2"},
            {"name": "Reset", "function": "q := reset * -1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Latch", "guard": "set == 1"},
            {"src": "Check", "tgt": "Reset", "guard": "reset == 1"},
            {"src": "Check", "tgt": "End", "guard": "set == 0 and reset == 0"},
            {"src": "Latch", "tgt": "End", "guard": "True"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["set", "reset", "q", "init"]
    },
    # 42. Minimum of three
    {
        "name": "Minimum of three (Upgraded)",
        "steps": [
            {"name": "Init", "function": "min1 := min(a, b)"},
            {"name": "Check", "function": ""},
            {"name": "Min2", "function": "min2 := min(min1, c)"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Min2", "guard": "True"},
            {"src": "Min2", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "c", "min1", "min2", "init"]
    },
    # 43. Maximum of three
    {
        "name": "Maximum of three (Upgraded)",
        "steps": [
            {"name": "Init", "function": "max1 := max(a, b)"},
            {"name": "Check", "function": ""},
            {"name": "Max2", "function": "max2 := max(max1, c)"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Max2", "guard": "True"},
            {"src": "Max2", "tgt": "End", "guard": "True"}
        ],
        "variables": ["a", "b", "c", "max1", "max2", "init"]
    },
    # 44. Set value if condition
    {
        "name": "Set value if condition (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := 0"},
            {"name": "Check", "function": ""},
            {"name": "Set", "function": "out := val * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Set", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Set", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "val", "out", "init"]
    },
    # 45. Reset to default if condition
    {
        "name": "Reset to default if condition (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := val + defval"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := defval * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["cond", "val", "defval", "out", "init"]
    },
    # 46. Sign Flip If Condition
    {
        "name": "Sign Flip If Condition (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "Flip", "function": "out := -input * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Flip", "guard": "cond == 1"},
            {"src": "Check", "tgt": "End", "guard": "cond == 0"},
            {"src": "Flip", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "cond", "out", "init"]
    },
    # 47. Reset If Negative
    {
        "name": "Reset If Negative (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input * 2"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := input + 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "input < 0"},
            {"src": "Check", "tgt": "End", "guard": "input >= 0"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "out", "init"]
    },
    # 48. Set to Max if Exceeds
    {
        "name": "Set to Max if Exceeds (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "SetMax", "function": "out := maxval * 2"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetMax", "guard": "input > maxval"},
            {"src": "Check", "tgt": "End", "guard": "input <= maxval"},
            {"src": "SetMax", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "maxval", "out", "init"]
    },
    # 49. Set to Min if Below
    {
        "name": "Set to Min if Below (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input"},
            {"name": "Check", "function": ""},
            {"name": "SetMin", "function": "out := minval - 1"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "SetMin", "guard": "input < minval"},
            {"src": "Check", "tgt": "End", "guard": "input >= minval"},
            {"src": "SetMin", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "minval", "out", "init"]
    },
    # 50. Reset If Out Of Bounds
    {
        "name": "Reset If Out Of Bounds (Upgraded)",
        "steps": [
            {"name": "Init", "function": "out := input * 2"},
            {"name": "Check", "function": ""},
            {"name": "Reset", "function": "out := input + maxval"},
            {"name": "End", "function": ""}
        ],
        "transitions": [
            {"src": "Init", "tgt": "Check", "guard": "init"},
            {"src": "Check", "tgt": "Reset", "guard": "input < minval or input > maxval"},
            {"src": "Check", "tgt": "End", "guard": "input >= minval and input <= maxval"},
            {"src": "Reset", "tgt": "End", "guard": "True"}
        ],
        "variables": ["input", "minval", "maxval", "out", "init"]
    },
]