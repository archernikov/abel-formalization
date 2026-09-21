#!/usr/bin/env python3
"""Run Palomar's pinned metadata/configuration checks on the local package.

This does not submit anything or replace the complete public preflight.
The pipeline checkout and its Python requirements must be installed separately.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys


PIPELINE_COMMIT = "3561d237dcc4b28482558ad28a64d767d7cc8615"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", required=True, type=Path)
    parser.add_argument("--licensee", type=Path, help="Path to bundle with Palomar's Gemfile installed")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    pipeline = args.pipeline.resolve()
    actual = subprocess.check_output(
        ["git", "-C", str(pipeline), "rev-parse", "HEAD"], text=True
    ).strip()
    if actual != PIPELINE_COMMIT:
        raise ValueError(f"Expected PalomarSubmission {PIPELINE_COMMIT}, got {actual}")
    sys.path.insert(0, str(pipeline))
    from scripts import submission_contract as contract
    from scripts import verify_submission as verifier

    metadata = contract.load_formalization_metadata(root / "formalization.yaml")
    config = verifier.load_comparator_config(root / "comparator.json")
    license_file = verifier.repository_license_file(root)
    if args.licensee:
        detected = verifier.detect_spdx_identifier(license_file, args.licensee.resolve())
        if detected != metadata["project"]["license"]:
            raise ValueError("Detected license does not match project.license")
        print(f"PASS: license detector reports {detected}")
    else:
        print("NOTE: SPDX detection omitted; CI runs the pinned license detector.")

    toolchain = (root / "lean-toolchain").read_text().strip()
    verifier.supported_toolchain(toolchain)
    packages = verifier.manifest_packages(root)
    challenge = root / verifier.module_source_suffix(config["challenge_module"])
    solution = root / verifier.module_source_suffix(config["solution_module"])
    for path in (challenge, solution):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing regular module source: {path.name}")
    raw = challenge.read_bytes()
    lines = len(raw.splitlines())
    if len(raw) > verifier.MAX_CHALLENGE_BYTES or lines > verifier.MAX_CHALLENGE_LINES:
        raise ValueError("Challenge exceeds Palomar's hard size limit")
    source = verifier.strip_lean_comments(raw.decode("utf-8"))
    imports = re.findall(r"^import\s+([\w.]+)\s*$", source, re.MULTILINE)
    if not imports or any(not name.startswith(("Mathlib.", "Lean.", "Init.")) for name in imports):
        raise ValueError("Challenge must import only Mathlib or Lean core modules")
    if config.get("enable_nanoda") is not True:
        raise ValueError("The standalone Comparator check requires enable_nanoda: true")

    print(f"PASS: Palomar metadata and Comparator configuration ({actual})")
    print(f"PASS: {len(packages)} pinned dependencies; {toolchain}")
    print(f"PASS: Challenge has {lines} lines and {len(raw)} bytes; library-only direct imports")
    print("Compared declarations: " + ", ".join(config["theorem_names"]))
    print("Full transitive import verification, proof replay, and registry review remain separate checks.")


if __name__ == "__main__":
    main()
