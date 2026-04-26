# 2026-04-26 — T1 (block_availability) closed

## What changed

Closed paper §5 **T1 (Block availability)** in `Beluga/Theorems.lean`,
leaving only T4 as a `sorry` in the post-GST liveness bundle.

### Helpers added

- **`step_advance_implies_stored`** — when `vid` advances by one round
  in a single `step`, every block `B ∈ s.blocks` with
  `hasAcceptedDigest s vid B.d` also has `hasStoredDigest s vid B.d`.
  Direct from `tryActFor`'s priority: doStore (action 3) sits above
  doAdvance (action 4), so when doAdvance fires the find? for the
  store-eligible block must have returned `none`. ~140 lines (mirror
  of `step_advance_implies_hasProposedFor`).
- **`find_advance_step`** — given vid at round `r` at trace `k₀` and
  round `≥ r + 1` at trace `k_target`, extracts the step `k_a ∈ [k₀,
  k_target)` at which vid is at `r` at trace `k_a` and at `r+1` at
  trace `(k_a+1)`. Induction on `Nat.le.rec`.

### T1 proof structure

Given `HasAccepted (trace k) vid d`:

1. Get post-GST step `k_post ≥ k` (`h_time.2`).
2. Get vid's currentRound at trace `k_post`, call it `r`.
3. Apply `h_fair` with target `r` (using vid as the witness honest
   validator) to get step `k_target` at which vid is at round
   `≥ r + 1`.
4. `find_advance_step` gives `k_a ∈ [k_post, k_target)` with vid at
   `r` at trace `k_a`, at `r + 1` at trace `(k_a + 1)`.
5. `step_advance_implies_stored` at trace `k_a`: for every
   `B ∈ (trace k_a).blocks`, `hasAcceptedDigest vid B.d → hasStoredDigest vid B.d`.
6. `acceptInv_trace` (using `hids : ValidIds system`, made public from
   private in this commit) gives `B ∈ (trace k_a).blocks` with
   `B.d = d`.
7. Combining: `hasStoredDigest (trace k_a) vid d`.
8. Recover the block witness from the `block_store vid B'` op.

### Bundle signature: `hids` added

`belugaTrace_satisfies_post_gst_liveness` now takes `hids : ValidIds
system` — needed by T1's invocation of `acceptInv_trace`. All wrapper
theorems (`lemma1_honest_round_entry`, `lemma2_round_latency`,
`theorem1_block_availability`, `theorem3_round_progression`,
`theorem4_round_termination`) thread `hids` through. The
`belugaTrace_isBlockSynchronizer` corollary already required `hids`
for T2 — it now passes it to T1/T3/T4 too.

### Made public

`acceptInv_trace` in `Protocol.lean` was `private`; promoted to
`theorem` so `Theorems.lean` can use it. (`causallyClosed_trace` was
already public; the underlying `AcceptInv` invariant is now also
exposed for downstream consumers.)

## Build state

`lake build` clean. Beluga/Theorems.lean: **1 sorry** (was 2) — only
T4 (round_termination) remaining. Mysticeti/Liveness.lean: 1 sorry
unchanged.

## What's next

T4 (round_termination): structurally similar to T3 but with the
accept-before-advance gate. At vid's first advance from `r` to
`r + 1`, the `allProposedFor system s r` gate ensures all registered
validators proposed for `r`; combined with the accept-disabled
condition (every B ∈ s.blocks either has B.d accepted by vid or has
an unaccepted parent), inductively vid has accepted all round-`r`
proposed blocks at that step. Counting via h_sys_nodup gives
≥ system.validators.length ≥ 2f+1 distinct authors. The induction on
round (parents accepted from prior rounds) is the structural
challenge.
