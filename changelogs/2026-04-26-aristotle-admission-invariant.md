# 2026-04-26 — Aristotle admission-invariant round: trace invariant + revised L13

## What changed

Integrated Aristotle project `9f17cf80-caba-4369-90b2-0a99a175e394`
(admission-invariant round, returned ~07:30 SGT, status
`COMPLETE_WITH_ERRORS` but **both target proofs are sorry-free**).

## Theorems closed

- **`belugaTrace_admissionWellFormed`** (in
  `Beluga/AdmissionInvariant.lean`): every block at round > 0 in the
  Beluga trace has ≥ 2f+1 distinct-author parents from the
  immediately preceding round, all themselves in the state.
- **`lemma13_cert_persistence`** (in `Mysticeti/Safety.lean`):
  certificate-persistence across rounds, proved via the paper §D.3
  quorum-intersection argument **derived inside the proof body**
  rather than assumed as an ad-hoc hypothesis.

## How

The trace invariant uses a *compound carrier* (`TraceInv`) tracking
four simultaneous properties:

1. `AdmissionWellFormed` itself.
2. Every `block_propose` op has its block in `state.blocks`.
3. Validators-IDs match the system's validator list.
4. Validators at round r > 0 satisfy `allProposedFor (r-1)`.

The carrier is preserved by every `tryActFor` branch
(`doPropose`/`doAccept`/`doStore`/`doAdvance`/no-op). The
`AdmissionWellFormed` projection follows.

L13 then uses this invariant as the source of `2f+1` parents for any
later block, applies `Quorum.quorumIntersection` against the `h_cert`
referencer set, pigeonholes an honest validator into the intersection
via the new helper `exists_honest_in_shared`, and identifies the
shared parent with the certificate via the new hypothesis
`h_honest_unique` (standard BFT: honest authors at most one block per
(author, round)).

## Effect on F-5 (mechanization findings)

**Item 1 closed.** "DAG admission well-formedness" is no longer a
hypothesis — it's a theorem about `belugaTrace`. We recommend the
paper add this as a named lemma alongside §D.3's L13.

Items 2–4 (view-traceback, decision-completeness, etc. from L16/T7)
remain.

## Build state

- `lake build` succeeds (6246 jobs).
- Sorry delta: −2. Both target files are sorry-free.
- New `set_option maxHeartbeats 800000` at the top of
  `AdmissionInvariant.lean` — necessary for `TraceInv`'s
  preservation proofs to typecheck.

## Aristotle attributions

- Project `9f17cf80` — see
  [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md)
  for full detail.

## What's next

- Two remaining in-flight rounds: `58873be7` (Beluga/Theorems
  L1-L2-T1-T4 under SchedulerFairness) and `3f6cf619` (Beluga/Protocol
  `causal_history_of_find_none`).
- After those return: focused round(s) on the 14 protocol-invariant
  sub-sorries in Mysticeti/Liveness left from round 5.
- F-7 (T7 safety/liveness boundary) still open — separate restatement
  decision required.
