#!/usr/bin/env python3
"""Build a compact self-contained catalog of every item in tactus-group-theory.
Dense format: per module, name@line grouped by kind. Minimizes size while listing everything."""
import os, re, sys, glob

SRC = os.path.join(os.path.dirname(__file__), "..", "src")
SRC = os.path.abspath(SRC)

# ---- parse lib.rs for per-module one-line purpose -------------------------
def module_purposes():
    lib = open(os.path.join(SRC, "lib.rs")).read().splitlines()
    purposes = {}
    buf = []
    for line in lib:
        s = line.strip()
        if s.startswith("//"):
            buf.append(s.lstrip("/").strip())
        elif s.startswith("pub mod ") or s.startswith("mod "):
            m = re.match(r'(?:pub )?mod (\w+);', s)
            if m:
                txt = " ".join(buf).strip()
                # first sentence-ish, cap length
                if txt:
                    # drop leading "modname:" label
                    txt = re.sub(r'^\w+:\s*', '', txt)
                    first = re.split(r'(?<=[.])\s', txt)[0]
                    if len(first) > 160:
                        first = first[:157] + "..."
                    purposes[m.group(1)] = first
            buf = []
        elif s.startswith("#["):
            pass  # keep buf across cfg attrs
        else:
            buf = []
    return purposes

# ---- parse a source file for items ----------------------------------------
FN_RE = re.compile(
    r'^\s*(?:pub(?:\((?:crate|super)\))?\s+)?'
    r'((?:default\s+|open\s+|closed\s+|uninterp\s+|broadcast\s+|axiom\s+|const\s+|unsafe\s+|async\s+)*)'
    r'(?:spec|proof|exec)?\s*'
    r'fn\s+([A-Za-z_]\w*)'
)
# capture modifier+kind more precisely by scanning tokens before 'fn'
KINDWORD_RE = re.compile(r'^\s*((?:pub(?:\([^)]*\))?\s+)?(?:[A-Za-z_]+\s+)*?)fn\s+([A-Za-z_]\w*)')
TYPE_RE = re.compile(r'^\s*(?:pub(?:\([^)]*\))?\s+)?(struct|enum|trait|type|union)\s+([A-Za-z_]\w*)')
BGROUP_RE = re.compile(r'^\s*(?:pub(?:\([^)]*\))?\s+)?broadcast\s+group\s+([A-Za-z_]\w*)')

def classify(prefix):
    toks = prefix.replace("pub", " ").split()
    toks = [t for t in toks if t and not t.startswith("(")]
    if "spec" in toks: return "spec"
    if "proof" in toks: return "proof"
    if "exec" in toks: return "exec"
    return "exec"  # bare fn = exec

def parse_file(path):
    items = {"spec": [], "proof": [], "exec": [], "type": [], "bgroup": []}
    lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    for i, line in enumerate(lines, 1):
        mb = BGROUP_RE.match(line)
        if mb:
            items["bgroup"].append((mb.group(1), i)); continue
        mt = TYPE_RE.match(line)
        if mt:
            items["type"].append((f"{mt.group(1)} {mt.group(2)}", i)); continue
        # function? require an actual ' fn <name>' with word boundary and not spec_fn/proof_fn types
        m = KINDWORD_RE.match(line)
        if m and re.search(r'(?<![A-Za-z_])fn\s+[A-Za-z_]', line):
            prefix, name = m.group(1), m.group(2)
            # guard against 'spec_fn(' type usages already excluded by requiring fn<space>name
            k = classify(prefix)
            items[k].append((name, i))
    return items, len(lines)

# ---- trust boundary / proof debt scan -------------------------------------
DEBT_RE = re.compile(r'(external_body|external\b|#\[verifier::external\]|assume\s*\(|admit\s*\(|assume_specification|\baxiom\b)')
def scan_debt(path):
    hits = []
    for i, line in enumerate(open(path, encoding="utf-8", errors="replace").read().splitlines(), 1):
        s = line.strip()
        if s.startswith("//"): continue
        for kw in ["external_body", "assume(", "assume (", "admit(", "admit (", "assume_specification", "#[verifier::external]"]:
            if kw in line:
                hits.append((kw.strip("(").strip(), i, s[:100]))
    return hits

def main():
    files = sorted(glob.glob(os.path.join(SRC, "*.rs")))
    purposes = module_purposes()
    data = {}
    debt = {}
    for f in files:
        mod = os.path.splitext(os.path.basename(f))[0]
        if mod == "lib": continue
        items, nlines = parse_file(f)
        data[mod] = (items, nlines)
        d = scan_debt(f)
        if d: debt[mod] = d
    # emit as python-repr for the builder step
    import json
    out = {"purposes": purposes,
           "data": {m: {"items": it, "lines": nl} for m,(it,nl) in data.items()},
           "debt": debt}
    json.dump(out, sys.stdout)

if __name__ == "__main__":
    main()
