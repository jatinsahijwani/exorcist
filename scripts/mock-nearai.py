#!/usr/bin/env python3
"""OFFLINE TEST ONLY: a fake OpenAI-compatible endpoint used to test the `exorcist draft` pipeline
(request, compile check, repair loop, assessment) without a NEAR AI key. Its "drafts" just call the
hand-written handlers, so they say nothing about how good real drafts are. Never used for results."""
import json
import re
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer

seen = {}

def draft_for(user, n_msgs):
    name = re.search(r"Use NAME = (\w+)", user).group(1)
    if "deployed at account `.token`" in user:
        body = "def handle := (tokenHandle : Ctx Acct → Call Acct → St Acct → Outcome (St Acct) Acct (Call Acct))"
    elif "deployed at account `.hook`" in user:
        body = "def handle := (hookHandle (.nat 0) : Ctx Acct → Call Acct → St Acct → Outcome (St Acct) Acct (Call Acct))"
    else:
        cfg = "{}"
        if "ghost_funds_bug` enabled" in user:
            cfg = "{ depositFixed := false }"
        if "withdraw_no_restore_bug` enabled" in user:
            cfg = "{ withdrawFixed := false }"
        body = f"def handle := vaultHandle ({cfg} : Config) Acct.token"
    broken = (name == "VaultFixed" and n_msgs <= 2)  # first attempt fails, to exercise the repair loop
    return (f"```lean\nimport Verifier.Models.Registry\nnamespace NearAsync.Vault.Draft.{name}\n"
            f"open NearAsync NearAsync.Vault\n{body}{' oops' if broken else ''}\n"
            f"end NearAsync.Vault.Draft.{name}\n```")

class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def do_POST(self):
        req = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        user = next(m["content"] for m in req["messages"] if m["role"] == "user")
        out = {"choices": [{"message": {"role": "assistant", "content": draft_for(user, len(req["messages"]))}}]}
        data = json.dumps(out).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

if __name__ == "__main__":
    HTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
