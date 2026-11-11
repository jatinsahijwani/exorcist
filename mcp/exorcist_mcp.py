#!/usr/bin/env python3
"""Exorcist MCP server (stdio, JSON-RPC 2.0, Python standard library only).

Tools:
  exorcist_check  {model, depth?}  -> bounded search over orderings x failures; JSON with verdict,
                                      attack trace, and deploy_allowed (false on any violation)
  exorcist_prove  {model, bounded?} -> kernel-checks the committed unbounded proof (or a bounded
                                      kernel-checked result); JSON with verdict and deploy_allowed
  exorcist_list   {}               -> the available models

Run from anywhere:  python3 mcp/exorcist_mcp.py   (needs `lake build` once in the repo)
Claude Code:        claude mcp add exorcist -- python3 /path/to/exorcist/mcp/exorcist_mcp.py
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "exorcist")
PROTOCOL = "2025-06-18"

TOOLS = [
    {
        "name": "exorcist_check",
        "description": (
            "Search every receipt ordering and failure (up to `depth` steps) of a NEAR contract model for "
            "a violation of its accounting invariant (ghost funds, stuck funds). Returns JSON: verdict, the "
            "shortest attack trace if any, and deploy_allowed (false if a violation exists). A 'no violation' "
            "verdict is bounded to the depth; call exorcist_prove for an all-traces proof."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "model": {"type": "string", "description": "model name, see exorcist_list"},
                "depth": {"type": "integer", "minimum": 1, "maximum": 12, "default": 10},
            },
            "required": ["model"],
        },
    },
    {
        "name": "exorcist_prove",
        "description": (
            "Kernel-check the committed Lean proof that the model's contract keeps its invariant for ALL "
            "traces (verdict proven_all_traces, deploy_allowed true). If the model has no unbounded proof, "
            "pass `bounded` (e.g. 4) for a kernel-checked result bounded to that depth."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "model": {"type": "string"},
                "bounded": {"type": "integer", "minimum": 1, "maximum": 6},
            },
            "required": ["model"],
        },
    },
    {
        "name": "exorcist_list",
        "description": "List the contract models Exorcist knows (name, vulnerable/fixed, pattern).",
        "inputSchema": {"type": "object", "properties": {}},
    },
]


def run(args, timeout=600):
    p = subprocess.run([EXE] + args, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr


def tool_check(a):
    model = str(a["model"])
    depth = int(a.get("depth", 10))
    code, out, err = run(["check", model, "--depth", str(depth), "--json", "-"])
    if code == 2:
        return {"error": (err or out).strip()}, True
    d = json.loads(out)
    v = d.get("violation") or {}
    res = {
        "model": model,
        "verdict": d["verdict"],
        "deploy_allowed": d["verdict"] != "violation",
        "states_explored": d["states_explored"],
        "bounds": d["bounds"],
        "liveness": [{"goal": g["goal"], "reachable": g["reachable"] == "true" or g["reachable"] is True}
                     for g in d.get("liveness", [])],
    }
    if d.get("disclaimer"):
        res["disclaimer"] = d["disclaimer"]
    if v:
        res["violation"] = {
            "kind": v["kind"], "depth": v["depth"], "witness_file": v["witness_file"],
            "trace": [
                {k: s[k] for k in ("i", "kind", "receiver", "method", "args", "outcome") if k in s}
                for s in v["trace"]
            ],
            "final_state": v["trace"][-1]["state_after"] if v["trace"] else None,
        }
        res["reason"] = f"attack found at depth {v['depth']} ({v['kind']}); do not deploy"
    else:
        res["reason"] = f"no violation within depth {depth} (bounded); run exorcist_prove for all traces"
    return res, False


def tool_prove(a):
    model = str(a["model"])
    args = ["prove", model, "--json"]
    if a.get("bounded"):
        args += ["--bounded", str(int(a["bounded"]))]
    code, out, err = run(args)
    line = next((l for l in out.splitlines() if l.startswith("{")), None)
    if line is None:
        return {"error": (err or out).strip()}, True
    return json.loads(line), False


def tool_list(_a):
    code, out, _ = run(["list"])
    models = []
    for l in out.splitlines():
        parts = l.split(None, 2)
        if len(parts) == 3:
            models.append({"name": parts[0], "kind": parts[1], "pattern": parts[2]})
    return {"models": models}, False


HANDLERS = {"exorcist_check": tool_check, "exorcist_prove": tool_prove, "exorcist_list": tool_list}


def reply(id_, result=None, error=None):
    msg = {"jsonrpc": "2.0", "id": id_}
    if error is not None:
        msg["error"] = error
    else:
        msg["result"] = result
    sys.stdout.write(json.dumps(msg) + "\n")
    sys.stdout.flush()


def handle(req):
    method, id_, params = req.get("method"), req.get("id"), req.get("params") or {}
    if id_ is None:  # notification (e.g. notifications/initialized)
        return
    if method == "initialize":
        reply(id_, {"protocolVersion": params.get("protocolVersion", PROTOCOL),
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "exorcist", "version": "0.1.0"}})
    elif method == "ping":
        reply(id_, {})
    elif method == "tools/list":
        reply(id_, {"tools": TOOLS})
    elif method == "tools/call":
        name, args = params.get("name"), params.get("arguments") or {}
        if name not in HANDLERS:
            reply(id_, error={"code": -32602, "message": f"unknown tool {name}"})
            return
        try:
            res, is_err = HANDLERS[name](args)
        except Exception as e:  # report tool failures as tool errors, not protocol errors
            res, is_err = {"error": str(e)}, True
        reply(id_, {"content": [{"type": "text", "text": json.dumps(res, indent=1)}],
                    "structuredContent": res, "isError": is_err})
    else:
        reply(id_, error={"code": -32601, "message": f"method not found: {method}"})


def main():
    if not os.path.exists(EXE):
        sys.stderr.write(f"exorcist binary not found at {EXE}; run `lake build` in {ROOT}\n")
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except json.JSONDecodeError:
            reply(None, error={"code": -32700, "message": "parse error"})
            continue
        handle(req)


if __name__ == "__main__":
    main()
