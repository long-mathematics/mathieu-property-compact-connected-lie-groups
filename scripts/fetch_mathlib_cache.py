#!/usr/bin/env python3
"""Fetch pinned mathlib caches for direct imports in proofs and audit helpers."""
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
paths = [ROOT / "MathieuProperty.lean", *sorted((ROOT / "MathieuProperty").rglob("*.lean")),
         *sorted((ROOT / "scripts").glob("*.lean"))]
modules = sorted({module for path in paths for module in re.findall(
    r"^import\s+(Mathlib(?:\.[A-Za-z0-9_]+)+)\s*$", path.read_text(), re.M)})
if not modules:
    raise SystemExit("No direct mathlib imports found")
print(f"Fetching {len(modules)} direct mathlib imports and their dependencies.", flush=True)
subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=ROOT, check=True,
               env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
