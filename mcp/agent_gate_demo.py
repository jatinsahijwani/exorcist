#!/usr/bin/env python3
"""A scripted 'AI coding agent' that must pass the Exorcist gate before deploying.

It speaks MCP to mcp/exorcist_mcp.py over stdio, exactly like an agent host would:
  1. wants to deploy the vault as written (withdraw-vulnerable)  -> gate says NO (attack trace)
  2. applies the fix (withdraw-fixed)                              -> check passes, prove passes -> YES
Exits non-zero if the gate does not behave like that, so it doubles as the integration test.
Deployment itself is simulated (printed), never performed.
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


class Client:
    def __init__(self):
        self.p = subprocess.Popen([sys.executable, os.path.join(HERE, "exorcist_mcp.py")],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.n = 0

    def call(self, method, params=None):
        self.n += 1
        self.p.stdin.write(json.dumps({"jsonrpc": "2.0", "id": self.n, "method": method,
                                       "params": params or {}}) + "\n")
        self.p.stdin.flush()
        return json.loads(self.p.stdout.readline())

    def notify(self, method):
        self.p.stdin.write(json.dumps({"jsonrpc": "2.0", "method": method}) + "\n")
        self.p.stdin.flush()

    def tool(self, name, **args):
        r = self.call("tools/call", {"name": name, "arguments": args})
        return r["result"]["structuredContent"]


def gate(c, model):
    print(f"\nagent> before deploying, call exorcist_check(model={model!r})")
    chk = c.tool("exorcist_check", model=model)
    print(f"gate>  verdict={chk['verdict']}  deploy_allowed={chk['deploy_allowed']}  ({chk['states_explored']} states)")
    if not chk["deploy_allowed"]:
        v = chk["violation"]
        print(f"gate>  {chk['reason']}")
        for s in v["trace"]:
            if s["kind"] == "refund":
                print(f"         {s['i']}. refund (1 yoctoNEAR deposit back to {s['receiver']})")
            else:
                print(f"         {s['i']}. {s['kind']:6} {s['receiver']}.{s['method']}  {s.get('outcome', '')}")
        print(f"gate>  final state: {json.dumps(v['final_state']['ft'])} ledger={json.dumps(v['final_state']['ledger'])}")
        return False
    print(f"agent> bounded check passed; call exorcist_prove(model={model!r})")
    pr = c.tool("exorcist_prove", model=model)
    print(f"gate>  verdict={pr['verdict']}  deploy_allowed={pr['deploy_allowed']}  theorems={pr['theorems']}")
    return pr["deploy_allowed"]


def main():
    c = Client()
    init = c.call("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                 "clientInfo": {"name": "agent-gate-demo", "version": "0"}})
    c.notify("notifications/initialized")
    names = [t["name"] for t in c.call("tools/list")["result"]["tools"]]
    print(f"connected to {init['result']['serverInfo']['name']}; tools: {', '.join(names)}")

    ok1 = gate(c, "withdraw-vulnerable")
    print("agent> DEPLOY BLOCKED. Fixing: restore the ledger in after_withdraw when ft_transfer failed." if not ok1
          else "agent> deploying (simulated)")
    ok2 = gate(c, "withdraw-fixed")
    print("agent> gate passed: deploying withdraw-fixed (simulated; nothing is sent to any network)" if ok2
          else "agent> DEPLOY BLOCKED")
    c.p.stdin.close()
    c.p.wait()
    if ok1 or not ok2:
        print("FAIL: the gate did not block the vulnerable contract and allow the fixed one")
        sys.exit(1)
    print("\nPASS: vulnerable contract blocked, fixed contract allowed")


if __name__ == "__main__":
    main()
