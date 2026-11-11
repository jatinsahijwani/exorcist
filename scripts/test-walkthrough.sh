#!/usr/bin/env bash
# End-to-end test of docs/WRITE-A-MODEL.md in a throwaway copy of the repo:
# scaffold a model, check + bounded prove it, introduce the documented bug, check finds it.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
TMP=$(mktemp -d "${TMPDIR:-/tmp}/exorcist-walkthrough.XXXXXX")
git ls-files -z --cached --others --exclude-standard | xargs -0 -I{} rsync -R {} "$TMP/" 2>/dev/null || git ls-files --cached --others --exclude-standard | while read -r f; do mkdir -p "$TMP/$(dirname "$f")"; cp "$f" "$TMP/$f"; done
[ -d .lake ] && cp -R .lake "$TMP/" || true
cd "$TMP"
E=./.lake/build/bin/exorcist
lake build exorcist >/dev/null
echo '$ exorcist new savings'; $E new savings
lake build exorcist >/dev/null
echo; echo '$ exorcist check savings'
set +e; $E check savings > check1.txt; c1=$?; set -e
sed -n '/^RESULT/,$p' check1.txt
echo; echo '$ exorcist prove savings --bounded 4'
set +e; $E prove savings --bounded 4 > prove1.txt; p1=$?; set -e
cat prove1.txt
# the documented bug: debit only in the success callback
python3 - <<'PY'
p='Verifier/Models/User/Savings.lean'; s=open(p).read()
old='''    .ok { s with ledger := s.ledger.sub ctx.pred amt }                    -- debit first
'''
new='''    .ok s                                                                  -- BUG: no debit here
'''
assert old in s; s=s.replace(old,new)
old2='''    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val .unit)  -- restore
    | _ => .ok s [] (.val .unit)'''
new2='''    | some (.ok _) => .ok { s with ledger := s.ledger.sub who amt } [] (.val .unit)  -- debit on success
    | _ => .ok s [] (.val .unit)'''
assert old2 in s; s=s.replace(old2,new2); open(p,'w').write(s)
PY
lake build exorcist >/dev/null
echo; echo '$ exorcist check savings   # after the bug'
set +e; $E check savings > check2.txt; c2=$?; set -e
sed -n '/^RESULT/,/kernel/p' check2.txt
echo
echo "exit codes: check=$c1 prove=$p1 check-after-bug=$c2"
if [ "$c1" = 0 ] && [ "$p1" = 0 ] && [ "$c2" = 1 ] && grep -q "checked by the Lean kernel" check2.txt; then
  echo "WALKTHROUGH PASS"; rm -rf "$TMP"
else
  echo "WALKTHROUGH FAIL (kept $TMP)"; exit 1
fi
