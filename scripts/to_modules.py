#!/usr/bin/env python3
"""Convert the Fad library to Lean's module system.

For every `Fad.lean` and `Fad/*.lean` file that does not start with `module` yet:

  * add `module` before the imports,
  * turn each `import X` into `public import X`,
  * open `@[expose] public section` after the imports, so that every
    declaration stays public and its body stays visible to `rfl`, `simp`,
    `decide` and `#eval` in other files (the behaviour before modules).

The script is idempotent: run it again after rebasing to convert new files.
Usage: python3 scripts/to_modules.py   (from the repository root)
"""
from __future__ import annotations
import pathlib
import re
import sys

IMPORT = re.compile(r"^import\s")


def convert(text: str) -> str | None:
    lines = text.splitlines(keepends=True)
    if any(l.strip() == "module" for l in lines):
        return None
    idx = [i for i, l in enumerate(lines) if IMPORT.match(l)]
    body_after = lines[idx[-1] + 1:] if idx else lines
    has_body = any(l.strip() for l in body_after)
    section = ["\n", "@[expose] public section\n"] if has_body else []
    if not idx:
        return "".join(["module\n"] + section + ["\n"] + lines)
    first, last = idx[0], idx[-1]
    out = lines[:first] + ["module\n", "\n"]
    out += ["public " + l if IMPORT.match(l) else l for l in lines[first:last + 1]]
    out += section + lines[last + 1:]
    return "".join(out)


def main() -> int:
    root = pathlib.Path(__file__).resolve().parent.parent
    files = [root / "Fad.lean", *sorted((root / "Fad").glob("*.lean"))]
    for f in files:
        new = convert(f.read_text())
        if new is not None:
            f.write_text(new)
            print(f"converted {f.relative_to(root)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
