#!/usr/bin/env python3
"""Mirror checks: a Lean module that mirrors an upstream OCaml file declares
the same constructors in the same order (design section 2.1).

Each pair below names an OCaml file of the pinned P4-SpecTec and the Lean
module that mirrors it. Constructors are read from type declarations only:
OCaml `type`/`and` blocks, Lean `inductive` blocks. The OCaml sequence must
be a subsequence of the Lean one (the Lean file may add helper inductives,
and flattens the polymorphic-variant unions). Exit 0 is the verdict.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
UP = ROOT / "upstream" / "p4-spectec" / "p4spec" / "lib"

# Types internal to an OCaml function's implementation, not mirrored.
SKIP = {"domain/mixfix.ml": {"atom_internal"}}

PAIRS = [
    ("lang/il/ast.ml", "P4SpecTec/IL/Ast.lean"),
    ("lang/al/ast.ml", "P4SpecTec/AL/Ast.lean"),
    ("domain/atom.ml", "P4SpecTec/Domain/Atom.lean"),
    ("domain/mixfix.ml", "P4SpecTec/Domain/Mixfix.lean"),
    ("lang/xl/num.ml", "P4SpecTec/Xl/Num.lean"),
    ("lang/xl/bool.ml", "P4SpecTec/Xl/Bool.lean"),
]


def ocaml_types(text):
    """Constructor lists of `type`/`and` declarations, by type name. A
    polymorphic-variant union `[ A.k | B.k ]` is recorded as the list of the
    module-qualified names it unions, marked with a leading `=`."""
    out, name = {}, None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("(*"):
            continue
        m = re.match(r"(?:type|and)\s+(?:\([^)]*\)\s+|'[a-z]\s+)?([a-z_][A-Za-z0-9_']*)", stripped)
        if m:
            name = m.group(1)
        elif re.match(r"(let|module|exception|val)\b", stripped):
            name = None
        if not name:
            continue
        body = line.split("=", 1)[1] if re.match(r"\s*(type|and)\b", line) and "=" in line else line
        # an inline variant in a constructor's payload is its own Lean inductive
        body = body.split(" of ", 1)[0] if " of " in body else body
        for u in re.findall(r"[|\[]\s*([A-Z][A-Za-z0-9_']*\.[a-z_]+)", body):
            out.setdefault(name, []).append("=" + u)
        for c in re.findall(r"[|\[]\s*`?([A-Z][A-Za-z0-9_']*)(?![\w.])", body):
            out.setdefault(name, []).append(c)
    return out


XL = {"Bool": "lang/xl/bool.ml", "Num": "lang/xl/num.ml"}


def expand_unions(types):
    """Replace union members by the constructors of the unioned types, in
    order: the IL flattens `[ Bool.unop | Num.unop ]` into one inductive."""
    cache = {}
    for name, ctors in types.items():
        expanded = []
        for c in ctors:
            if c.startswith("="):
                mod, tname = c[1:].split(".")
                if mod not in cache:
                    cache[mod] = ocaml_types((UP / XL[mod]).read_text())
                expanded.extend(cache[mod].get(tname, []))
            else:
                expanded.append(c)
        types[name] = expanded
    return types


def lean_types(text):
    """Constructor lists of `inductive` declarations, by type name."""
    out, name = {}, None
    for line in text.splitlines():
        stripped = line.strip()
        m = re.match(r"inductive\s+([A-Za-z_][A-Za-z0-9_'.]*)", stripped)
        if m:
            name = m.group(1)
        elif re.match(r"(def|abbrev|instance|theorem|partial|private|end|namespace|open|structure)\b", stripped):
            name = None
        m = re.match(r"\s*\|\s+([A-Za-z_][A-Za-z0-9_']*)", line)
        if name and m:
            out.setdefault(name, []).append(m.group(1))
    return out


def main():
    fail = 0
    for ml, lean in PAIRS:
        a = expand_unions(ocaml_types((UP / ml).read_text()))
        b = lean_types((ROOT / lean).read_text())
        bad = []
        for tname, ctors in a.items():
            if tname in SKIP.get(ml, set()):
                continue
            if tname not in b:
                bad.append(f"{tname}: not an inductive in Lean")
            elif b[tname] != ctors:
                bad.append(f"{tname}: OCaml {ctors} vs Lean {b[tname]}")
        if bad:
            fail = 1
            print(f"[check-mirror] {lean} does not mirror {ml}:")
            for line in bad:
                print(f"  {line}")
        else:
            n = sum(len(c) for c in a.values())
            print(f"[check-mirror] {lean} mirrors {ml} ({len(a)} types, {n} constructors)")
    return fail


if __name__ == "__main__":
    sys.exit(main())
