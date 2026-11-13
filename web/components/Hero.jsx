"use client";

import Link from "next/link";
import { useRef } from "react";
import { PixelHero } from "./PixelHero";
import { REPO } from "./Topbar";

export function Hero() {
  const slot = useRef(null);
  return (
    <section className="hero">
      <PixelHero slotRef={slot} />
      <div className="hero-body">
        <a className="hero-chip" href="#incident" data-clear>
          <span className="dot" aria-hidden />
          Found automatically: the Oct 2026 NEAR Intents mechanism, in 8 steps
        </a>
        <div className="hero-slot" ref={slot} role="img" aria-label="EXORCIST" />
        <h1 className="cursor" data-clear>Finds ghost funds in NEAR contracts, or proves there are none.</h1>
        <p className="sub" data-clear>
          A Lean 4 model of NEAR async execution and NEP-141. A bounded search finds the shortest attack and the Lean kernel
          re-checks it; fixed contracts are proven solvent for every trace of the model; every trace is replayed on real
          Rust contracts in the NEAR sandbox.
        </p>
        <div className="ctas" data-clear>
          <Link className="btn primary" href="/viewer/">
            Watch the attack, step by step →
          </Link>
          <a className="btn secondary" href={REPO}>
            Source, proofs and docs
          </a>
        </div>
      </div>
    </section>
  );
}
