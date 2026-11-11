# Agent gate: an AI coding agent may deploy only what Exorcist accepts

AI agents now write and ship contracts. An agent with deploy rights should not be trusted to notice
an async accounting bug in its own code. `mcp/exorcist_mcp.py` is a small MCP server (stdio,
Python standard library only) that gives any MCP-capable agent two tools:

| Tool | Input | Returns |
|---|---|---|
| `exorcist_check` | `{model, depth?}` | verdict, `deploy_allowed` (false on any violation), the shortest attack trace, bounds, liveness |
| `exorcist_prove` | `{model, bounded?}` | verdict `proven_all_traces` / `vulnerable` / `no_unbounded_proof` / `kernel_checked_bounded_to_depth_N`, `deploy_allowed`, theorem names, `#print axioms` |
| `exorcist_list` | `{}` | the available models |

The policy you give the agent: *before any deploy, call `exorcist_check`; deploy only if
`deploy_allowed` is true; then call `exorcist_prove` and deploy only on `proven_all_traces`.*
The tools return structured JSON (`structuredContent`) as well as text.

## Do X → see Y

```sh
lake build                       # once
python3 mcp/agent_gate_demo.py   # or: make test-mcp
```

`agent_gate_demo.py` is a scripted agent that talks MCP to the server over stdio, like an agent host
does. It tries to ship the vault as written, gets blocked, applies the fix, and is allowed. It exits
non-zero if the gate does not block the first and allow the second, so it runs in CI and in `make demo`.
Deploys are simulated (printed); nothing is sent to any network. Actual output:

```
connected to exorcist; tools: exorcist_check, exorcist_prove, exorcist_list

agent> before deploying, call exorcist_check(model='withdraw-vulnerable')
gate>  verdict=violation  deploy_allowed=False  (3622 states)
gate>  attack found at depth 5 (funds_stuck); do not deploy
         1. submit vault.withdraw  
         2. run    vault.withdraw  ok
         3. fail   token.ft_transfer  failed
         4. run    vault.after_withdraw  ok
         5. refund (1 yoctoNEAR deposit back to vault)
gate>  final state: {"alice": 0, "eve": 100, "vault": 100, "hook": 0} ledger={"alice": 0, "eve": 0}
agent> DEPLOY BLOCKED. Fixing: restore the ledger in after_withdraw when ft_transfer failed.

agent> before deploying, call exorcist_check(model='withdraw-fixed')
gate>  verdict=no_violation_bounded_to_depth_10  deploy_allowed=True  (11154645 states)
agent> bounded check passed; call exorcist_prove(model='withdraw-fixed')
gate>  verdict=proven_all_traces  deploy_allowed=True  theorems=['withdraw_fixed_solvent_all_traces', 'withdraw_fixed_no_stuck_all_traces']
agent> gate passed: deploying withdraw-fixed (simulated; nothing is sent to any network)

PASS: vulnerable contract blocked, fixed contract allowed
```

## Use it from an agent

Claude Code:

```sh
claude mcp add exorcist -- python3 /path/to/exorcist/mcp/exorcist_mcp.py
```

Any other MCP host: run `python3 /path/to/exorcist/mcp/exorcist_mcp.py` as a stdio server.

Raw protocol, one call (`tools/call` → `exorcist_check` on `deposit-vulnerable`), result excerpt:

```json
{
 "model": "deposit-vulnerable",
 "verdict": "violation",
 "deploy_allowed": false,
 "states_explored": 444,
 "bounds": {
  "depth": 10,
  "actors": [
 …
```

## Limits

The gate is only as good as the model of the contract (see the README's limits). A model the agent
writes itself must be reviewed by a human; otherwise the agent could gate itself with a convenient
model. `deploy_allowed` from `exorcist_check` alone is a bounded result; require
`exorcist_prove` → `proven_all_traces` for contracts that have a proof.
