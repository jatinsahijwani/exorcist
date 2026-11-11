#!/usr/bin/env python3
"""Record the README demo: run the real commands, save an asciicast v2 file (docs/media/demo.cast,
playable with `asciinema play`) and an animated SVG (docs/media/demo.svg) for the README.
Usage: python3 scripts/record-demo.py   (after `lake build`; runs `make demo` for the last scene)"""
import html
import json
import os
import re
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E = "./.lake/build/bin/exorcist"
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.path.expanduser("~/.cargo/bin") + ":" + os.environ["PATH"])


def run(cmd):
    t0 = time.time()
    out = subprocess.run(cmd, shell=True, cwd=ROOT, env=ENV, capture_output=True, text=True).stdout
    return out, time.time() - t0


def scene_incident():
    out, dt = run(f"{E} check incident-2026-10")
    lines = out.splitlines()
    keep = [l for l in lines if l.startswith("NOTE") or l.startswith("RESULT")]
    trace = lines[lines.index(next(l for l in lines if l.startswith("RESULT"))) + 2:]
    for l in trace:
        if l.startswith("Witness theorem"):
            break
        keep.append(l)
    keep += [l for l in lines if "checked by the Lean kernel" in l]
    return "exorcist check incident-2026-10", keep, dt


def scene_prove():
    out, dt = run(f"{E} prove incident-2026-10-fixed")
    keep = [l for l in out.splitlines() if l.startswith(("NOTE", "statement", "           transactions", "RESULT", "axioms"))]
    return "exorcist prove incident-2026-10-fixed", keep, dt


def scene_demo():
    out, dt = run("make demo")
    lines = out.splitlines()
    i = max(k for k, l in enumerate(lines) if "SUMMARY" in l)
    keep = [re.sub(r"\x1b\[[0-9;]*m", "", l) for l in lines[i + 1:] if l.strip()]
    return "make demo", keep, dt


def write_cast(scenes, path):
    with open(path, "w") as f:
        f.write(json.dumps({"version": 2, "width": 110, "height": 34, "title": "Exorcist demo",
                            "env": {"TERM": "xterm-256color", "SHELL": "/bin/zsh"}}) + "\n")
        t = 0.5
        for cmd, lines, dt in scenes:
            f.write(json.dumps([round(t, 2), "o", f"\x1b[2J\x1b[H$ {cmd}\r\n"]) + "\n")
            t += min(dt, 2.0) + 0.3
            for l in lines:
                f.write(json.dumps([round(t, 2), "o", l + "\r\n"]) + "\n")
                t += 0.12
            t += 3.0


def color(l):
    if l.startswith("$ "):
        return "#e5c07b"
    if any(k in l for k in ("⚠", "VIOLATION", "FAIL ")) and "PASS" not in l[:6]:
        return "#e06c75"
    if any(k in l for k in ("✓", "PASS", "PROVEN", "ALL PASS")):
        return "#98c379"
    if l.startswith(("NOTE", "axioms")):
        return "#7f8c98"
    return "#d7dae0"


def write_svg(scenes, path, width=980, lh=16.5, maxlines=30):
    # timeline: each scene shows its command, then lines appear one by one, then holds
    events, t = [], 0.0
    for cmd, lines, _ in scenes:
        lines = lines[: maxlines - 1]
        start = t
        appear = [t + 0.6 + 0.09 * k for k in range(len(lines))]
        end = appear[-1] + 4.0 if lines else t + 3
        events.append((cmd, lines, start, appear, end))
        t = end
    total = t
    pct = lambda x: f"{100 * x / total:.3f}%"
    h = int(40 + lh * maxlines + 16)
    css, body = [], []
    for si, (cmd, lines, start, appear, end) in enumerate(events):
        css.append(f"@keyframes s{si}{{0%{{opacity:0}}{pct(start)}{{opacity:0}}{pct(start + 0.01)}{{opacity:1}}"
                   f"{pct(end - 0.01)}{{opacity:1}}{pct(end)}{{opacity:0}}100%{{opacity:0}}}}")
        body.append(f'<g style="animation:s{si} {total:.2f}s linear infinite;opacity:0">')
        body.append(f'<text x="16" y="{40 + lh:.1f}" fill="#e5c07b">$ {html.escape(cmd)}</text>')
        for k, (l, ta) in enumerate(zip(lines, appear)):
            css.append(f"@keyframes l{si}_{k}{{0%{{opacity:0}}{pct(ta)}{{opacity:0}}{pct(ta + 0.01)}{{opacity:1}}100%{{opacity:1}}}}")
            y = 40 + lh * (k + 2)
            body.append(f'<text x="16" y="{y:.1f}" fill="{color(l)}" style="animation:l{si}_{k} {total:.2f}s linear infinite;opacity:0">'
                        f'{html.escape(l)}</text>')
        body.append("</g>")
    svg = (f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{h}" viewBox="0 0 {width} {h}" '
           f'role="img" aria-label="Exorcist demo: finds the attack, proves the fix, make demo summary">'
           f'<style>text{{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:11.5px;white-space:pre}}'
           f'{"".join(css)}</style>'
           f'<rect width="{width}" height="{h}" rx="8" fill="#1e2127"/>'
           f'<circle cx="18" cy="16" r="5" fill="#e06c75"/><circle cx="36" cy="16" r="5" fill="#e5c07b"/>'
           f'<circle cx="54" cy="16" r="5" fill="#98c379"/>'
           f'<text x="{width / 2:.0f}" y="20" fill="#7f8c98" text-anchor="middle">exorcist — finds ghost funds in NEAR contracts, or proves there are none</text>'
           f'{"".join(body)}</svg>')
    with open(path, "w") as f:
        f.write(svg)


if __name__ == "__main__":
    scenes = [scene_incident(), scene_prove(), scene_demo()]
    write_cast(scenes, os.path.join(ROOT, "docs/media/demo.cast"))
    write_svg(scenes, os.path.join(ROOT, "docs/media/demo.svg"))
    os.makedirs(os.path.join(ROOT, "docs/site/media"), exist_ok=True)
    write_svg(scenes, os.path.join(ROOT, "docs/site/media/demo.svg"))
    print("wrote docs/media/demo.cast and docs/media/demo.svg")
