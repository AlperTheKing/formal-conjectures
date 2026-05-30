import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path.cwd()
INVENTORY = ROOT / "scratch" / "open_erdos_inventory.jsonl"
RESULTS = ROOT / "scratch" / "shallow_results.jsonl"
LAKE = Path(r"C:\Users\a\.elan\bin\lake.exe")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_TIMEOUT = int(os.environ.get("LEAN_TIMEOUT", "45"))
MAX_WORKERS = int(os.environ.get("LEAN_WORKERS", "16"))


def code_part(s: str) -> str:
    idx = s.find("--")
    return s if idx < 0 else s[:idx]


def theorem_signature_from(text: str, start_offset: int) -> str:
    pos = start_offset
    out = []
    while pos < len(text):
        line_end = text.find("\n", pos)
        if line_end < 0:
            line_end = len(text)
            line = text[pos:line_end]
            newline = ""
        else:
            line = text[pos:line_end]
            newline = "\n"
        cp = code_part(line)
        by_idx = cp.find(":= by")
        if by_idx >= 0:
            out.append(line[: by_idx + len(":= by")])
            break
        out.append(line + newline)
        pos = line_end + 1
    return "".join(out).rstrip("\n")


def namespace_stack_before(lines: list[str], line_no_1_based: int) -> list[str]:
    stack: list[str] = []
    for line in lines[: line_no_1_based - 1]:
        stripped = line.strip()
        if stripped.startswith("namespace "):
            parts = stripped.split()
            if len(parts) >= 2:
                stack.extend(parts[1].split("."))
        elif stripped == "end":
            if stack:
                stack.pop()
        elif stripped.startswith("end "):
            parts = stripped.split()
            if len(parts) >= 2 and stack:
                end_parts = parts[1].split(".")
                if stack[-len(end_parts) :] == end_parts:
                    del stack[-len(end_parts) :]
                else:
                    stack.pop()
    return stack


def full_name(record: dict, text: str) -> str:
    lines = text.splitlines()
    stack = namespace_stack_before(lines, record["start_line"])
    name = record["theorem"]
    if stack and not name.startswith(".".join(stack) + "."):
        return ".".join(stack + [name])
    return name


def abs_offset_for_line_col(text: str, line_no_1_based: int, col: int) -> int:
    offset = 0
    lines = text.splitlines(keepends=True)
    for line in lines[: line_no_1_based - 1]:
        offset += len(line)
    return offset + col


def replace_first_sorry_after(text: str, offset: int, proof_body: str) -> str | None:
    m = re.search(r"\bsorry\b", text[offset:])
    if not m:
        return None
    start = offset + m.start()
    end = offset + m.end()
    return text[:start] + proof_body + text[end:]


def axiom_gate(output: str) -> tuple[bool, str]:
    if "sorryAx" in output:
        return False, "sorryAx in #print axioms output"
    m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", output)
    if not m:
        return True, "no axioms listed"
    axioms = {x.strip() for x in m.group(1).split(",") if x.strip()}
    extra = axioms - ALLOWED_AXIOMS
    if extra:
        return False, "disallowed axioms: " + ", ".join(sorted(extra))
    return True, "allowed axioms: " + ", ".join(sorted(axioms))


def check_candidate(record: dict, attempt: int, proof_body: str, label: str) -> dict:
    source_path = ROOT / record["file"]
    text = source_path.read_text(encoding="utf-8")
    sig_offset = abs_offset_for_line_col(text, record["start_line"], 0)
    sig = theorem_signature_from(text, sig_offset)
    if sig != record["signature"]:
        return {
            "theorem": record["theorem"],
            "file": record["file"],
            "attempt": attempt,
            "label": label,
            "status": "reject",
            "reason": "original signature parser mismatch",
        }

    proof_offset = abs_offset_for_line_col(
        text, record["signature_end_line"], record["signature_end_col"]
    )
    patched = replace_first_sorry_after(text, proof_offset, proof_body)
    if patched is None:
        return {
            "theorem": record["theorem"],
            "file": record["file"],
            "attempt": attempt,
            "label": label,
            "status": "reject",
            "reason": "no sorry token found after signature",
        }

    patched_sig = theorem_signature_from(patched, sig_offset)
    if patched_sig != record["signature"]:
        return {
            "theorem": record["theorem"],
            "file": record["file"],
            "attempt": attempt,
            "label": label,
            "status": "reject",
            "reason": "patched signature changed",
        }

    banned = ["sorry", "admit", "native_decide", "axiom "]
    if any(tok in proof_body for tok in banned):
        return {
            "theorem": record["theorem"],
            "file": record["file"],
            "attempt": attempt,
            "label": label,
            "status": "reject",
            "reason": "banned token in proof body",
        }

    safe_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", record["theorem"])
    scratch = ROOT / "scratch" / f"check_{safe_name}_a{attempt}_{label}.lean"
    target = full_name(record, text)
    scratch.write_text(patched + f"\n\n#print axioms {target}\n", encoding="utf-8")

    start = time.time()
    try:
        proc = subprocess.run(
            [str(LAKE), "env", "lean", str(scratch)],
            cwd=ROOT,
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            timeout=LEAN_TIMEOUT,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "theorem": record["theorem"],
            "file": record["file"],
            "attempt": attempt,
            "label": label,
            "status": "timeout",
            "seconds": round(time.time() - start, 3),
            "scratch": str(scratch.relative_to(ROOT)),
            "reason": "lean timeout",
        }

    output = (proc.stdout or "") + (proc.stderr or "")
    gate_ok, gate_reason = axiom_gate(output)
    result = {
        "theorem": record["theorem"],
        "file": record["file"],
        "attempt": attempt,
        "label": label,
        "status": "pass" if proc.returncode == 0 and gate_ok else "fail",
        "returncode": proc.returncode,
        "seconds": round(time.time() - start, 3),
        "scratch": str(scratch.relative_to(ROOT)),
        "target": target,
        "axiom_gate": gate_reason,
        "proof_body": proof_body,
    }
    if proc.returncode != 0:
        lines = [ln for ln in output.splitlines() if "error:" in ln or "warning:" in ln]
        result["diagnostic"] = "\n".join(lines[:8])
    elif not gate_ok:
        result["diagnostic"] = gate_reason
    return result


def main() -> int:
    results_path = ROOT / os.environ.get("RESULTS", "scratch/shallow_results.jsonl")
    records = [
        json.loads(line)
        for line in INVENTORY.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if results_path.exists():
        done = {
            (json.loads(line)["theorem"], json.loads(line).get("attempt"))
            for line in results_path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
    else:
        done = set()

    if os.environ.get("PROOF_CANDIDATES_JSON"):
        candidates = [
            (idx + 1, item["label"], item["body"])
            for idx, item in enumerate(json.loads(os.environ["PROOF_CANDIDATES_JSON"]))
        ]
    else:
        candidates = [
            (1, "simpa", "simpa"),
            (2, "aesop", "aesop"),
        ]
    targets = None
    if os.environ.get("TARGETS"):
        targets = {x.strip() for x in os.environ["TARGETS"].split(",") if x.strip()}
    jobs = []
    for record in records:
        if record.get("needs_human_review"):
            continue
        if targets is not None and record["theorem"] not in targets and record.get("full_name") not in targets:
            continue
        for attempt, label, body in candidates:
            if (record["theorem"], attempt) not in done:
                jobs.append((record, attempt, body, label))

    print(json.dumps({"pending_jobs": len(jobs), "results": str(results_path)}, ensure_ascii=False))
    results_path.parent.mkdir(exist_ok=True)
    with results_path.open("a", encoding="utf-8") as fh:
        with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futs = [pool.submit(check_candidate, *job) for job in jobs]
            for fut in concurrent.futures.as_completed(futs):
                result = fut.result()
                fh.write(json.dumps(result, ensure_ascii=False) + "\n")
                fh.flush()
                sys.stdout.write(json.dumps(result, ensure_ascii=False) + "\n")
                sys.stdout.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
