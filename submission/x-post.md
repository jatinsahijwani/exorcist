# X post draft (Jatin posts it; attach the demo video)

**Main post**

A NEAR contract can credit a deposit, have a later call fail, and watch the token refund it. The ledger keeps the credit: ghost funds.

I built Exorcist at #NEARHackathon. It finds the attack trace in your contract model, or proves in Lean that none exists for any trace.

Video ↓ Repo: <REPO_URL>

@NEARProtocol @NearLegion @NearBuilders

**Reply 1 (how it works)**

How it works:
• Lean model of NEAR async receipts and the NEP-141 refund flow
• explores every receipt ordering and failure, prints the shortest attack, kernel-checks it
• replays each trace against real Rust contracts in the NEAR sandbox
• proves the fixed vault solvent for all traces

**Reply 2 (question)**

Question for NEAR builders: which cross-contract pattern in your contracts would you most want checked next? Callbacks after ft_transfer, NFT transfers with callbacks, or promise joins?

---
Notes
- First line states the user problem; the NEAR role is concrete (async receipts, NEP-141 refunds, sandbox, NEAR AI Cloud for the optional proof loop).
- Contains @NEARProtocol and #NEARHackathon (required); @NearLegion and @NearBuilders are optional.
- Replace <REPO_URL> after the repo is public. Attach the video (screenshots alone are not enough for a local-only demo, per Q-012).
