#!/usr/bin/python3

import oscat_data as data

def translate(out, pname:str, structure):
    name = structure["name"]

    out.write(f"// {name}\n\n")

    out.write(f"PROGRAM {pname}\n")
    variables = structure["variables"]
    if "input" in variables:
        variables.remove("input")
        out.write("  VAR_INPUT\n    input : INT;\n  END_VAR\n")

    if "output" in variables:
        variables.remove("output")
        out.write("  VAR_OUTPUT\n    output : INT;\n  END_VAR\n")

    out.write("  VAR\n")
    other = ', '.join(variables)
    out.write(f"    {other} : INT;\n")
    out.write("  END_VAR\n\n\n")

    for step in structure["steps"]:
        name = step["name"]
        out.write(f"  ACTION act_{name}\n")
        if step['function']:
            out.write(f"    {step['function']};\n")
        out.write(f"  END_ACTION\n\n")


    for step in structure["steps"]:
        name = step["name"]
        init = "Init" == name

        if init:
            out.write(f"  INITIAL_STEP ") 
        else: 
            out.write(f"  STEP ") 
        
        out.write(step["name"]+"\n")
        out.write(f"    : act_{name}(N);\n")
        out.write("  END_STEP\n\n")

    out.write("\n")
    for trans in structure['transitions']:
         src = trans['src']
         tgt = trans['tgt']
         cond = trans["guard"]
         out.write(f"  TRANSITION FROM {src} TO {tgt}\n    := {cond};\n  END_TRANSITION\n")
          
    out.write("END_PROGRAM")

for idx, (old,new) in enumerate(zip(data.oscat_examples, data.oscat_examples_upgraded)):
    idx += 1
    with open(f"../{idx}_standard.st", 'w') as fh:
        translate(fh, "standard", old)

    with open(f"../{idx}_upgraded.st", 'w') as fh:
        translate(fh, "upgraded", new)