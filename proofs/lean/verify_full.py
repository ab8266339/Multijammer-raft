"""Rebuild and audit the independent supplement on BRJD (WSL -> native Lean)."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LAKE = "/mnt/c/Users/admin/.elan/bin/lake.exe"
EVIDENCE = ROOT / "evidence"
EVIDENCE.mkdir(exist_ok=True)
MODULES = {
    "R260402Multijammer": "R260402",
    "R260402Supplement": "R260402Supplement",
    "R260402Geometry": "R260402Geometry",
    "R260402QuorumLimit": "R260402QuorumLimit",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "R260402Multijammer": "bec0c8d03b67dce3ea2a6bb9217e2bd7d224aaa86dd277e50490dd663f49f0bc",
    "R260402Supplement": "763e264be87b32521a8ccf2677d1736a9e4bef23befd0bf36ea8946bf1dc2e25",
}


def run(label, args):
    p = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, encoding="utf-8", errors="strict")
    (EVIDENCE / (label + ".log")).write_text(p.stdout, encoding="utf-8")
    (EVIDENCE / (label + ".exit")).write_text(str(p.returncode) + "\n", encoding="ascii")
    print(label + ": exit " + str(p.returncode), flush=True)
    if p.returncode:
        print(p.stdout[-12000:], flush=True)
        sys.exit(p.returncode)
    return p.stdout


def uncomment(text):
    # Lex nested Lean block comments, line comments, and quoted strings.
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j == -1 else j
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, "Unclosed comment"
    return "".join(out)


sources, declarations = [], []
for module, namespace in MODULES.items():
    path = ROOT / (module + ".lean")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if module in EXPECTED:
        assert digest == EXPECTED[module], (module, "legacy input changed")
    clean = uncomment(path.read_text(encoding="utf-8-sig"))
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|proof_wanted)\b", clean)
    assert not forbidden, (module, forbidden)
    found = re.findall(r"(?m)^(?:noncomputable\s+)?(theorem|lemma|def|structure)\s+([\w']+)", clean)
    assert found, module
    names = [namespace + "." + name for _, name in found]
    declarations.extend(names)
    sources.append({"file": path.name, "sha256": digest,
                    "theoremsAndLemmas": sum(k in {"theorem", "lemma"} for k, _ in found),
                    "auditedDeclarations": len(names)})

audit = "import R260402Proofs\n\n" + "\n".join("#print axioms " + n for n in declarations) + "\n"
(ROOT / "AxiomAudit.lean").write_text(audit, encoding="utf-8")
version = run("lean_version", [LAKE, "env", "lean", "--version"])
run("full_build", [LAKE, "build"])
audit_output = run("axiom_audit", [LAKE, "env", "lean", "AxiomAudit.lean"])
results = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit_output):
    axioms = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    assert axioms <= ALLOWED, (m.group(1), axioms)
    results[m.group(1)] = sorted(axioms)
assert set(results) == set(declarations), ("missing audit records", set(declarations) - set(results))
manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib["rev"] == "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
report = {
    "dateInUserTimezone": "2026-11-06", "timezone": "Asia/Shanghai",
    "completedUtcReportedByBRJD": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "machine": "DESKTOP-BRJD313", "project": str(ROOT),
    "leanVersion": version.strip(), "mathlibCommit": mathlib["rev"],
    "buildExitCode": 0, "axiomAuditExitCode": 0,
    "theoremsAndLemmas": sum(s["theoremsAndLemmas"] for s in sources),
    "auditedDeclarations": len(results), "allowedAxioms": sorted(ALLOWED),
    "forbiddenConstructScan": "passed", "sources": sources, "axioms": results,
    "acceptedTexSha256": "52492e4f0fea79b186978c7e14c67bdee9dadc8ba4323367c51a2a3bf2a57bd7",
    "scope": ["Full finite-sum quorum asymptotics for every p in [0,1] and all n",
              "General finite-jammer analytic ray decomposition"],
    "acceptedManuscriptModified": False,
}
(EVIDENCE / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print("PASS: " + str(report["theoremsAndLemmas"]) + " theorems/lemmas, " + str(len(results)) + " declarations audited", flush=True)
