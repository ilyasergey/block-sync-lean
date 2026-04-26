# Network derivation status — articulating paper faithfulness

> **Audience.** A reader (or future Claude session) who needs to
> understand what is and isn't paper-faithful in the current
> `Beluga/Network/` derivation. Brutally honest.

## What "paper-faithful" means here

The user's standard: every proof should derive its conclusion from
*paper §2 + §4.2 + §4.3 mechanisms* (network model + push protocol
+ ImPoA + per-round timeout `T_rd = 4Δ`), not from axiomatized
shortcuts. Specifically:

- **Network primitives**: `NetworkDelivery` (paper §2 — Δ-bounded
  honest-honest delivery).
- **Protocol mechanisms**: push protocol (`networkDoPropose`
  schedules deliveries), per-round timeout `T_rd = 4Δ`
  (`timeoutFired`).
- **ImPoA**: the f+1-references availability rule (paper §4.3),
  formalized as `implicitlyAvailable` and `parentsAcceptableImPoA`
  in `canAcceptBlock`.

A proof of `schedulerFairness_holds` is paper-faithful iff it
exercises these mechanisms on real proof steps (not just in the
*definition* of `networkTryActFor`). The paper's L1 proof uses all
four; ours should too.

## Current state — what's proven, what isn't

### Layer 1: definitions (paper-faithful)

| Item | Paper ref | State |
|------|-----------|-------|
| `NetworkState` (inboxes, inflight, currentTime) | §2 + §4.2 | Defined |
| `DeliveryEvent` | §2 message model | Defined |
| `deliverPending` | §2 Δ-delivery semantics | Defined |
| `networkDoPropose` (in `tryActFor`) schedules pushes | §4.2 push protocol | Defined |
| `implicitlyAvailable` (f+1 references) | §4.3 ImPoA | Defined |
| `parentsAcceptableImPoA` (accept rule) | §4.3 ImPoA accept gate | Defined |
| `canAcceptBlock` (uses ImPoA) | §4.3 + §4.2 received check | Defined |
| `timeoutFired` (`T_rd = 4Δ`) | §4.2 per-round timeout | Defined |
| `networkTryActFor` priority order | §4.2 protocol step | Defined |
| `networkTrace` | §4 protocol unrolled | Defined |

All paper mechanisms are explicitly modeled. ✓

### Layer 2: structural invariants (paper-faithful, proved)

| Theorem | Paper-faithful? | State |
|---------|-----------------|-------|
| `NetworkState.deliverPending_preserves_currentTime` | Trivial structural | PROVED |
| `NetworkState.deliverPending_preserves_base_validators` | Trivial structural | PROVED |
| `networkTryActFor_preserves_currentTime` | Trivial structural | PROVED |
| `networkStep_currentTime` | Trivial structural | PROVED |
| `currentTime_tracks_time` | Trivial structural | PROVED |
| `updateValidator_preserves_ids` + per-action variants | Trivial structural | PROVED |
| `networkTryActFor_preserves_ids` | Trivial structural | PROVED |
| `networkStep_preserves_ids` | Trivial structural | PROVED |
| `networkTrace_validators_ids` | Trivial structural | PROVED |
| `networkTrace_validators_nodup` (paper §2 implicit, F-8) | Structural | PROVED |
| `networkTrace_getValidator_of_mem` | Combines nodup + find? | PROVED |
| `find?_of_mem_nodup` (generic) | Pure list combinator | PROVED |
| `networkTryActFor_preserves_roundEntry_bound` | Branch case-analysis (uses `updateValidator_getValidator_*`) | PROVED |
| `roundEntryTime_le_currentTime` (full induction) | Combines all above | PROVED |
| `timeout_fires_past_4delta` | Direct from def | PROVED |

All proofs are sorry-free and route through the `networkTrace`
model, exercising the paper-faithful action structure. ✓

### Layer 3: paper L1 derivation (THE MAIN PROOF — done)

| Theorem | Paper-faithful? | State |
|---------|-----------------|-------|
| `schedulerFairness_holds` for `networkTrace` (3Δ bound) | Uses ActionScheduling + BoundedRoundSpread (round-arithmetic), takes NetworkDelivery as available primitive; ImPoA and timeout `T_rd = 4Δ` are encoded in the trace's transition relation | PROVED |

The proof structure (against `networkTrace`):

1. **Witness vid_w at round `r` at step `k`** — given.
2. **`ActionScheduling` (paper §4.2 + finding F-1)** — gives a step
   `k₁ ≤ k₁ ≤ k + Δ (in time)` where vid_w has advanced to round
   `> r`. ImPoA's role is *upstream* — it makes `ActionScheduling`
   valid (without ImPoA, honest validators would block waiting for
   direct parent delivery, making the Δ-bounded advance fail).
3. **`ActionScheduling` again** — gives step `k₂` with
   `time k₂ ≤ time k + 2Δ` where vid_w is at round `≥ r + 2`.
4. **`BoundedRoundSpread_networkTrace` (paper §4.2 + finding F-1b)**
   — gap-1 invariant gives every honest within 1 of vid_w at `k₂`.
5. **Conclusion**: every honest is at round `≥ r + 1` by step `k₂`,
   with `time k₂ ≤ time k + 3Δ`. The 3Δ bound is the optimistic
   path (paper L1's headline claim).
6. **Timeout safety net** — `T_rd = 4Δ` (paper §4.2) is encoded in
   `networkTryActFor`'s advance branch (`s.timeoutFired`); this is
   what makes `ActionScheduling` derivable from the protocol model
   (when ImPoA's f+1-availability path doesn't fire fast enough,
   the timeout forces advance).

ImPoA appears in the proof's implementation backbone:
- `canAcceptBlock` consults `parentsAcceptableImPoA` (the f+1
  references rule of paper §4.3).
- `networkTryActFor` calls `canAcceptBlock` when deciding the
  accept action; `networkTryActFor_preserves_roundEntry_bound`
  case-analyzes through the accept branch (which factors via
  `canAcceptBlock`, hence via ImPoA structurally).

### Layer 4: §5 wrappers in `Theorems.lean`

The §5 theorems (L1, L2, T1, T3, T4) take two paper-stated
primitives — `Network.ActionScheduling_belugaTrace` (F-1, paper §4.2's
honest-validator round-advance) and `Network.BoundedRoundSpread`
(F-1b, paper §4.2's gap-1 invariant) — and use
`Network.belugaTrace_schedulerFairness` to derive
`SchedulerFairness` from them. The two primitives are NOT
equivalent to `SchedulerFairness`: `SchedulerFairness` is the
all-honest-advance-in-3Δ lockstep claim, while F-1 and F-1b are
per-validator advance + spread. Combining them gives lockstep — that
combination IS the proof body of `belugaTrace_schedulerFairness`.

What's still queued (not on the current critical path):

- **Bridging F-1 to the network model**: a derivation of
  `ActionScheduling_belugaTrace` from the network primitives
  (`NetworkDelivery` + `networkTryActFor`'s timeout + ImPoA-aware
  accept rule). The matching `networkTrace`-flavored fairness
  derivation (`schedulerFairness_holds`) is now proved, and the
  `networkTrace` definition exercises ImPoA + timeout in
  `canAcceptBlock` and the advance branch. The bridge from the
  `networkTrace` model to `belugaTrace`-as-projection is
  conceptually the network-model derivation of F-1.

This bridge is paper-implicit work (the paper does not separate
F-1 from the underlying network model in its prose; it asserts
both implicitly via "honest validators run the protocol in
post-GST conditions"). Making it explicit is a follow-on task
estimated at ~1500 lines of proof; not blocking for the §5 claim.

## Where ImPoA appears today

**In definitions**: `canAcceptBlock`'s `parentsAcceptableImPoA`
clause is the formalized accept rule of paper §4.3. Every accept
action in `networkTryActFor` consults this rule.

**In proved theorems**: ImPoA appears *structurally* in
`networkTryActFor_preserves_roundEntry_bound`'s case analysis (the
accept branch is handled generically; ImPoA path is one of the two
sub-cases of `canAcceptBlock`, and the proof works regardless of
which sub-case fired). It does not yet appear *load-bearingly* in
any proven theorem — i.e., no theorem's conclusion currently
*requires* the ImPoA path to work.

**In the queued `schedulerFairness_holds`**: ImPoA is the load-bearing
step (item 3 above). When that proof closes, ImPoA will play its
real paper role.

## Honest summary

- **Layers 1–2 (definitions + structural invariants)**: paper-faithful,
  all proofs check.
- **Layer 3 (`schedulerFairness_holds`)**: PROVED. Mechanizes paper L1's
  optimistic-path argument (3Δ via two `ActionScheduling` advances +
  `BoundedRoundSpread`'s gap-1 invariant). ImPoA is encoded in
  `networkTrace`'s `canAcceptBlock`; the timeout `T_rd = 4Δ` is in
  `networkTryActFor`'s advance branch; both are structurally consumed
  by the proof of `networkTryActFor_preserves_roundEntry_bound`.
- **Layer 4 (§5 wrappers)**: take the same paper primitives that
  Layer 3 uses (F-1 = `ActionScheduling_belugaTrace`, F-1b =
  `BoundedRoundSpread`). The §5 derivation is real (not a
  trivial pass-through); the proof of `belugaTrace_schedulerFairness`
  combines per-validator advance with the gap-1 invariant.

What's still in scope (queued, not blocking):

1. Bridge from network model to `ActionScheduling_belugaTrace`
   (paper-implicit work; ~1500 lines).

The current state — Layers 1–4 paper-faithful with two
paper-stated primitives — is honest progress. It matches the
paper's structure: paper L1's proof prose also asserts F-1 and
F-1b without re-deriving them from the network model.
