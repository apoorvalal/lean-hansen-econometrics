# /// script
# requires-python = ">=3.10"
# ///
"""Worklist resolver + finding-schema validator for the Lean review harness."""
import json, sys, argparse, re
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCHEMA = json.loads((REPO / "review" / "finding-schema.json").read_text())

def _check(obj, schema, path=""):
    """Tiny validator for the subset of JSON Schema we use. Returns error str or None."""
    t = schema.get("type")
    if t == "object" or "properties" in schema:
        if not isinstance(obj, dict):
            return f"{path or 'root'}: expected object"
        for req in schema.get("required", []):
            if req not in obj:
                return f"{path}{req}: required field missing"
        if schema.get("additionalProperties") is False:
            for k in obj:
                if k not in schema.get("properties", {}):
                    return f"{path}{k}: unexpected field"
        for k, sub in schema.get("properties", {}).items():
            if k in obj:
                err = _check(obj[k], sub, f"{path}{k}.")
                if err:
                    return err
        return None
    if "enum" in schema:
        return None if obj in schema["enum"] else f"{path[:-1]}: {obj!r} not in {schema['enum']}"
    if t == "string":
        return None if isinstance(obj, str) else f"{path[:-1]}: expected string"
    if t == "integer":
        if not isinstance(obj, int) or isinstance(obj, bool):
            return f"{path[:-1]}: expected integer"
        if "minimum" in schema and obj < schema["minimum"]:
            return f"{path[:-1]}: below minimum"
        return None
    if t == "boolean":
        return None if isinstance(obj, bool) else f"{path[:-1]}: expected boolean"
    return None

def validate_schema(stream) -> int:
    try:
        findings = json.load(stream)
    except json.JSONDecodeError as e:
        print(f"invalid JSON on stdin: {e}", file=sys.stderr)
        return 2
    if not isinstance(findings, list):
        findings = [findings]
    for i, f in enumerate(findings):
        err = _check(f, SCHEMA, "")
        if err:
            print(f"finding[{i}]: {err}", file=sys.stderr)
            return 1
    return 0

def resolve_paths(files: list[str]) -> list[dict]:
    """Resolve a list of Lean file paths to their chapter metadata."""
    results = []
    for path in files:
        m = re.search(r"Chapter(\d+)", path)
        if m:
            n = int(m.group(1))
            entry = {
                "file": path,
                "chapter": n,
                "excerpt_path": f"textbook/ch{n:02d}/ch{n:02d}_excerpt.txt",
                "inventory_path": f"inventory/ch{n}-inventory.md",
                "decls": [],
            }
        else:
            entry = {
                "file": path,
                "chapter": None,
                "excerpt_path": None,
                "inventory_path": None,
                "decls": [],
            }
        results.append(entry)
    return results


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--validate-schema", action="store_true")
    sub = p.add_subparsers(dest="command")
    resolve_p = sub.add_parser("resolve", help="Resolve chapter/path metadata for Lean files")
    resolve_p.add_argument("files", nargs="+")
    args = p.parse_args(argv)
    if args.validate_schema:
        return validate_schema(sys.stdin)
    if args.command == "resolve":
        print(json.dumps(resolve_paths(args.files)))
        return 0
    p.error("no command given")

if __name__ == "__main__":
    sys.exit(main())
