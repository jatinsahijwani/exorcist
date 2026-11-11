# X post draft (Jatin posts it; attach the demo video)

**Main post**

A NEAR contract credited deposits, an attacker failed the next call, the token refunded, the credits stayed: $3.8M in ghost funds.

Exorcist, built at #NEARHackathon, finds that attack by itself and proves the fix in Lean for every trace.

<REPO_URL> @NEARProtocol

**Reply 1 (how it works)**

How it works:
• Lean model of NEAR async receipts + NEP-141 refunds
• every ordering × failure explored, shortest attack kernel-checked
• traces replayed on Rust contracts in the NEAR sandbox
• MCP gate: AI agents deploy only what passes

@NearLegion @NearBuilders

**Reply 2 (question)**

NEAR builders: which cross-contract pattern in your contracts would you want checked next? Withdraw callbacks, NFT transfer-call, or promise joins? Reply and I'll model one.

---
Notes
- The first line states the user problem. NEAR's role is concrete: async receipts, NEP-141 refunds,
  the sandbox, and NEAR AI Cloud for the optional AI loops.
- @NEARProtocol and #NEARHackathon are required (main post); @NearLegion and @NearBuilders are optional (reply 1).
- The incident was on Oct 1, 2026 (withdrawals Sept 29 – Oct 1); the funds were returned.
- "Minimal model" is deliberate: we modelled the published mechanism, not the NEAR Intents contract.
  Keep that wording if you edit the post.
- Replace <REPO_URL> once the repo is public, and attach the video (Q-012).
