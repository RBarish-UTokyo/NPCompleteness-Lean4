#!/usr/bin/env python3
"""Preflight for the Palomar submission rules that can be checked without Lean.

Checks the repository layout, Lean source rules, the Challenge's size and
imports, comparator.json, the licence file, and the mechanically checked fields
of formalization.yaml, following Palomar's submission standard
(https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
It also checks that Challenge.lean matches its generator. It does not build
anything; `scripts/palomar_dryrun.sh` runs this script and then the Lean checks.

The formalization.yaml checks need PyYAML (`pip install pyyaml`); without it
they are skipped with a warning. Names in brackets, such as
"[to be completed before submission]", are placeholders: they produce a warning,
and with --submission an error.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

try:
    import tomllib
except ImportError:  # Python < 3.11
    tomllib = None

ROOT = Path(__file__).resolve().parents[1]
MINIMUM_TOOLCHAIN = (4, 35, 0, "rc2")
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
COMPARATOR_KEYS = {"challenge_module", "solution_module", "theorem_names",
                   "permitted_axioms", "definition_names", "enable_nanoda"}
SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
RELATIONSHIPS = {"formalizes", "adapts", "independently-proves", "background", "other"}
LICENCE_NAMES = {"license", "licence", "copying", "unlicense", "ofl"}
COMPILED_SUFFIXES = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so",
                     ".trace"}
CORE_IMPORT = re.compile(r"(Init|Std|Lean)(\.|$)")

errors: list[str] = []
warnings: list[str] = []


def error(message: str) -> None:
    errors.append(message)


def physical_lines(data: bytes) -> int:
    """Lines as Palomar counts them: LF and CRLF end a line, and so does EOF."""
    text = data.replace(b"\r\n", b"\n")
    return text.count(b"\n") + (0 if text.endswith(b"\n") or not text else 1)


def strip_comments(source: str) -> str:
    """Remove (nested) block comments, line comments and string literals."""
    out, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            depth += pair == "/-"
            depth -= pair == "-/"
            i += 2 if pair in ("/-", "-/") else 1
        elif pair == "/-":
            depth, i = 1, i + 2
        elif pair == "--":
            j = source.find("\n", i)
            i = len(source) if j == -1 else j
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            out.append('""')
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def count_token(code: str, token: str) -> int:
    return len(re.findall(rf"(?<![\w.'`]){token}(?![\w'])", code))


def repository_files() -> list[Path]:
    try:
        listed = subprocess.run(["git", "ls-files", "-z", "--cached", "--others",
                                 "--exclude-standard"], cwd=ROOT, check=True,
                                capture_output=True).stdout.split(b"\0")
        files = [ROOT / name.decode() for name in listed if name]
        return [path for path in files if path.exists() or path.is_symlink()]
    except (OSError, subprocess.CalledProcessError):
        return [path for path in ROOT.rglob("*")
                if not {".git", ".lake"} & set(path.relative_to(ROOT).parts)
                and (path.is_file() or path.is_symlink())]


def check_layout(files: list[Path]) -> None:
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    match = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-(rc\d+))?", toolchain)
    if not match:
        error(f"lean-toolchain must name a Lean release, not {toolchain!r}")
    else:
        major, minor, patch, rc = match.groups()
        version = (int(major), int(minor), int(patch), rc or "~")  # a release sorts after its rcs
        if version < MINIMUM_TOOLCHAIN:
            error(f"lean-toolchain {toolchain} is older than Palomar's minimum")
    lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (ROOT / name).exists()]
    if len(lakefiles) != 1:
        error("the project root must contain exactly one of lakefile.toml and lakefile.lean")
    elif lakefiles[0] == "lakefile.toml":
        data = (ROOT / "lakefile.toml").read_bytes()
        if len(data) > 1 << 20:
            error("lakefile.toml is larger than 1 MiB")
        if tomllib is not None:
            tomllib.loads(data.decode())
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest.get("packages", []):
        if package.get("type") == "git":
            url, rev = package.get("url", ""), package.get("rev", "")
            if not re.fullmatch(r"https://github\.com/[\w.-]+/[\w.-]+", url.removesuffix(".git")):
                error(f"dependency {package.get('name')} must use a public GitHub URL")
            if not re.fullmatch(r"[0-9a-f]{40}", rev):
                error(f"dependency {package.get('name')} must be pinned to a full commit SHA")
    if (ROOT / ".gitmodules").exists():
        error("Git submodules are not accepted")
    licences = [path.name for path in ROOT.iterdir() if path.is_file()
                and path.name.lower().split(".")[0] in LICENCE_NAMES
                and path.suffix.lower() in ("", ".md", ".markdown", ".txt")]
    if len(licences) != 1:
        error(f"the root must contain exactly one licence file, found {licences}")
    size = 0
    for path in files:
        relative = path.relative_to(ROOT)
        if path.suffix in COMPILED_SUFFIXES:
            error(f"compiled build output is committed: {relative}")
        if path.is_symlink():
            if path.suffix == ".lean":
                error(f"symbolic links to Lean files are refused: {relative}")
            continue
        size += path.stat().st_size
        if path.stat().st_size < 1024 and path.read_bytes().startswith(
                b"version https://git-lfs.github.com/spec/"):
            error(f"Git LFS pointer: {relative}")
    if size > 500 << 20:
        error("the repository is larger than 500 MiB")


def check_lean_sources(files: list[Path], challenge: Path) -> None:
    for path in files:
        if path.suffix != ".lean" or path.is_symlink():
            continue
        relative = path.relative_to(ROOT)
        data = path.read_bytes()
        if physical_lines(data) > 10_000:
            error(f"{relative} has more than 10,000 lines")
        if path.name == "lakefile.lean":
            continue
        code = strip_comments(data.decode())
        if code.split()[:1] != ["module"]:
            error(f"{relative} does not start with the `module` header")
        if path != challenge:
            for token in ("sorry", "admit", "native_decide", "axiom"):
                if count_token(code, token):
                    error(f"{relative} contains `{token}`")


def check_challenge(challenge: Path, theorems: list[str]) -> None:
    data = challenge.read_bytes()
    lines = physical_lines(data)
    if lines > 1000 or len(data) > 100 * 1024:
        error(f"Challenge.lean exceeds the hard limits ({lines} lines, {len(data)} bytes)")
    elif lines > 300 or len(data) > 32 * 1024:
        warnings.append(f"Challenge.lean has {lines} lines and {len(data)} bytes; "
                        "above 300 lines or 32 KiB Palomar gives a warning")
    code = strip_comments(data.decode())
    for imported in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", code, re.M):
        if not CORE_IMPORT.match(imported):
            error(f"Challenge.lean imports {imported}, which is not Lean core")
    if count_token(code, "sorry") != len(theorems):
        error("Challenge.lean should contain exactly one `sorry` per compared theorem")
    result = subprocess.run([sys.executable, str(ROOT / "scripts/generate_challenge.py"),
                             "--check"], capture_output=True, text=True)
    if result.returncode != 0:
        error(result.stderr.strip() or "Challenge.lean differs from its generator")


def check_comparator() -> list[str]:
    config = json.loads((ROOT / "comparator.json").read_text())
    if not isinstance(config, dict):
        error("comparator.json must contain one JSON object")
        return []
    for key in ("challenge_module", "solution_module", "theorem_names", "permitted_axioms"):
        if key not in config:
            error(f"comparator.json lacks {key}")
    if set(config) - COMPARATOR_KEYS:
        error(f"comparator.json has keys Palomar does not accept: {set(config) - COMPARATOR_KEYS}")
    theorems = config.get("theorem_names", [])
    if not theorems or not all(isinstance(name, str) and name for name in theorems):
        error("comparator.json needs a nonempty list of theorem names")
    if not set(config.get("permitted_axioms", [])) <= PERMITTED_AXIOMS:
        error("comparator.json permits an axiom outside propext, Quot.sound, Classical.choice")
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        error("this preflight expects the Challenge and Solution modules")
    return theorems


def nonempty_strings(value: object) -> bool:
    return isinstance(value, list) and bool(value) and all(
        isinstance(item, str) and item.strip() for item in value)


def check_metadata(submission: bool) -> None:
    try:
        import yaml
    except ImportError:
        warnings.append("PyYAML is not installed; formalization.yaml was not checked")
        return
    data = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    project = data.get("project", {})
    name, description = project.get("name"), project.get("description")
    if not isinstance(name, str) or not 0 < len(name) <= 300:
        error("project.name must be a nonempty string of at most 300 characters")
    if not isinstance(description, str) or not 0 < len(description) <= 10_000:
        error("project.description must be a nonempty string of at most 10,000 characters")
    for field in ("authors", "responsible_maintainers"):
        names = project.get(field)
        if not nonempty_strings(names):
            error(f"project.{field} must be a nonempty list of names")
        elif any(name.strip().startswith("[") for name in names):
            message = f"project.{field} still contains a placeholder name"
            if submission:
                error(message)
            else:
                warnings.append(message)
    licence = (ROOT / "LICENSE").read_text(encoding="utf-8")
    if project.get("license") != "Apache-2.0" or "Apache License" not in licence \
            or "Version 2.0, January 2004" not in licence:
        error("project.license must match the licence in LICENSE (Apache-2.0)")
    classification = data.get("classification", {})
    arxiv, msc = classification.get("arxiv", []), classification.get("msc2020", [])
    if not 1 <= len(arxiv) <= 8 or len(set(arxiv)) != len(arxiv):
        error("classification.arxiv needs one to eight distinct codes")
    if len(msc) > 8 or len(set(msc)) != len(msc):
        error("classification.msc2020 allows at most eight distinct codes")
    methods = data.get("automation", {}).get("methods")
    if not isinstance(methods, list) or not methods or not all(
            isinstance(method, dict) and method.get("method") for method in methods):
        error("automation.methods needs entries with a method")
    if not data.get("review", {}).get("status"):
        error("review.status is required")
    sources = data.get("sources")
    if not isinstance(sources, list) or not sources:
        error("sources must be a nonempty list")
        return
    for source in sources:
        if not source.get("title") or source.get("relationship") not in RELATIONSHIPS:
            error(f"source {source.get('title')!r} needs a title and a valid relationship")
        if "type" in source and source["type"] not in SOURCE_TYPES:
            error(f"source {source.get('title')!r} has a type Palomar does not accept")
    relationships = {source.get("relationship") for source in sources}
    if any(source.get("type") == "original-proof" for source in sources) or \
            not relationships & {"formalizes", "adapts", "independently-proves"}:
        error("sources must describe a source-based result")
    if "repository" in data:
        error("omit `repository`: this repository is the substantive development")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--submission", action="store_true",
                        help="also reject placeholder author and maintainer names")
    args = parser.parse_args()
    files = repository_files()
    challenge = ROOT / "Challenge.lean"
    check_layout(files)
    theorems = check_comparator()
    check_lean_sources(files, challenge)
    check_challenge(challenge, theorems)
    check_metadata(args.submission)
    for message in warnings:
        print(f"warning: {message}")
    for message in errors:
        print(f"error: {message}", file=sys.stderr)
    if errors:
        return 1
    print("Submission preflight passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
