#!/usr/bin/env python3
"""Reject proof placeholders and extra foundational declarations in project Lean sources."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|unsafe)\b")


def code_only(text: str) -> str:
    """Blank comments and strings, preserving line numbers and nested block comments."""
    output = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                output[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                output[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    output[i] = " "
                i += 1
        elif text.startswith("/-", i):
            output[i:i + 2] = "  "
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            output[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            output[i] = " "
            i += 1
            while i < len(text):
                ch = text[i]
                output[i] = "\n" if ch == "\n" else " "
                i += 1
                if ch == "\\" and i < len(text):
                    output[i] = "\n" if text[i] == "\n" else " "
                    i += 1
                elif ch == '"':
                    break
        else:
            i += 1
    return "".join(output)


files = sorted(p for p in ROOT.rglob("*.lean")
               if ".lake" not in p.relative_to(ROOT).parts and ".git" not in p.parts)
errors = []
for path in files:
    code = code_only(path.read_text())
    for match in FORBIDDEN.finditer(code):
        line = code.count("\n", 0, match.start()) + 1
        errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden token {match.group()}")
# Every mathematical module must be reachable from the default umbrella target.
modules = {"MathieuProperty." + ".".join(p.relative_to(ROOT / "MathieuProperty").with_suffix("").parts): p
           for p in (ROOT / "MathieuProperty").rglob("*.lean")}
modules["MathieuProperty"] = ROOT / "MathieuProperty.lean"
visited, pending = set(), ["MathieuProperty"]
while pending:
    module = pending.pop()
    if module in visited:
        continue
    visited.add(module)
    for dependency in re.findall(r"^import\s+(MathieuProperty(?:\.[A-Za-z0-9_]+)*)\s*$",
                                 code_only(modules[module].read_text()), re.M):
        if dependency not in modules:
            errors.append(f"Missing project import: {dependency}")
        else:
            pending.append(dependency)
for module in sorted(modules.keys() - visited):
    errors.append(f"Module not imported by the build umbrella: {module}")
if errors:
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"Source audit passed: {len(files)} Lean files; no forbidden proof tokens.")
