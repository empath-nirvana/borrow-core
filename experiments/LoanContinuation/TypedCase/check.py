#!/usr/bin/env python3
"""Check the isolated typed scalar-loan experiment against this checkout's Core."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys


here = Path(__file__).resolve().parent
repo = here.parents[2]
source_roots = (
    (repo, repo / "Core" / "Chain" / "SI" / "LoanX", "Core.Chain.SI.LoanX"),
    (here / "ProofTree", here / "ProofTree" / "TypedCaseProof", "TypedCaseProof"),
)
output_root = repo / ".lake" / "build" / "lib" / "lean"

sources: dict[str, tuple[Path, Path]] = {}
for root, module_dir, prefix in source_roots:
    for source in module_dir.rglob("*.lean"):
        name = prefix + "." + ".".join(source.relative_to(module_dir).with_suffix("").parts)
        if name in sources:
            raise SystemExit(f"duplicate module: {name}")
        sources[name] = (root, source)

if not sources or not any(name.startswith("TypedCaseProof.") for name in sources):
    raise SystemExit("Core LoanX or TypedCaseProof sources are missing")

order: list[str] = []
visiting: set[str] = set()
visited: set[str] = set()


def visit(name: str) -> None:
    if name in visited:
        return
    if name in visiting:
        raise SystemExit(f"import cycle at {name}")
    visiting.add(name)
    source = sources[name][1]
    for line in source.read_text().splitlines():
        if line.startswith("import "):
            for dep in line.removeprefix("import ").split():
                if dep in sources:
                    visit(dep)
    visiting.remove(name)
    visited.add(name)
    order.append(name)


for module in sorted(sources):
    visit(module)

lake_path = subprocess.check_output(
    ["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, text=True
).strip()
lean = subprocess.check_output(
    ["lake", "env", "which", "lean"], cwd=repo, text=True
).strip()
env = os.environ.copy()
env["LEAN_PATH"] = f"{output_root}{os.pathsep}{lake_path}"

log: list[str] = []
for name in order:
    root, source = sources[name]
    output = output_root.joinpath(*name.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        [lean, "-R", str(root), "-o", str(output), str(source)],
        cwd=repo,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    print(f"{name}: {'ok' if result.returncode == 0 else 'FAILED'}", flush=True)
    log.append(f"### {name} (exit {result.returncode})\n{result.stdout}")
    if result.returncode:
        (here / "check.log").write_text("\n".join(log))
        print(result.stdout, file=sys.stderr)
        raise SystemExit(result.returncode)

(here / "check.log").write_text("\n".join(log))
print(f"Checked {len(order)} modules; details in {here / 'check.log'}")
