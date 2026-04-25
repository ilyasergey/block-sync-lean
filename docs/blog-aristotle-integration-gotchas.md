# Integrating Aristotle output: a field guide

A blog seed for the operational lessons learned wiring Aristotle
(Harmonic) into a real Lean 4 formalization. The conceptual companion
is [math-tactical-wall.md](math-tactical-wall.md); this document
collects the *gotchas* — concrete patterns that bit us, with the
file/project-ID receipts so a future post can ground each claim.

The point of a blog post on this isn't "Aristotle is bad". It's that
*integration is its own engineering problem*: Aristotle solves the
tactical wall, but mating its output with a working repository takes
a small repertoire of hand-edits that are easy to miss and easy to
re-derive once you've seen them.

## Gotcha 1 — `import Mathlib` blows up the linker

**Symptom.** Aristotle's tarball ships `import Mathlib` at the top of
every file it touched. On macOS, `clang` then refuses to link the
project executable: "argument list too long". Build fails *after*
the proofs check, which is maximally confusing.

**Fix.** Narrow to `import Mathlib.Tactic` (or even narrower —
`Mathlib.Data.List.Basic`, `Mathlib.Order.Basic`, etc.) — Aristotle's
proofs almost always work unchanged with the narrower import. We've
done this in every Aristotle-touched file so far:

- [`Validation.lean`](../BlockSynchroniser/Validation.lean) — round 1 (be7c0245)
- [`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean) — round 3d (84e08b81)
- [`Beluga/PerformanceLemmas.lean`](../BlockSynchroniser/Beluga/PerformanceLemmas.lean) — round 3e (91c97602)
- [`Beluga/StepPreservation.lean`](../BlockSynchroniser/Beluga/StepPreservation.lean) — round 3e (91c97602)

**Why this happens.** `import Mathlib` is the path of least resistance
for Aristotle: it removes any need to identify the specific theorem
being used. Cheap from Aristotle's perspective; expensive on the
build side.

## Gotcha 2 — `exact?` left as placeholder in production

**Symptom.** Build error like:
```
info: ...: Try this:
  [apply] exact Or.inr h_find
```
Aristotle returned a proof with `exact?` still in it, expecting the
suggestion to be applied. The hint *is* the proof — but `exact?` itself
is a search, not a tactic that closes the goal.

**Fix.** Read the "Try this:" hint and substitute literally. In round
3e (project 91c97602) we replaced two occurrences:
```
exact?  ⟶  exact Or.inr h_find
exact?  ⟶  exact init_getValidator_honest system vid h
```

**Why this happens.** Aristotle's training/search loop sometimes treats
`exact?` as a usable closure. The result is closure-by-suggestion: the
goal is closed by the linter info message, not by the tactic. Lean
trusts neither.

## Gotcha 3 — `▸` cast mismatches and how to dodge them

**Symptom.** Aristotle aggressively uses `▸` (rewrite arrow) to apply
a hypothesis after a `match`/`split`. Lean rejects with:
```
invalid `▸` notation, expected result type of cast is
  ...
however, the equality
  ...
does not contain the expected result type on either the left or the
right hand side
```

**Fix.** `▸` requires the equality to *literally appear* in the goal.
In `match`/`split_ifs` branches the goal often contains a residue of
the case discriminant; Lean can't see the equality. Replace with
`convert ... using 1` or `refine`. We've queued
[`tryActFor_preserves_reputation`](../BlockSynchroniser/Beluga/StepPreservation.lean)
as a 3e-followup (project bb79d236) with explicit guidance to avoid `▸`.

**Why this happens.** Aristotle's beam-search rewards short syntactic
proofs; `▸` is shorter than `convert`. But `convert` is robust under
cast mismatches.

## Gotcha 4 — `simp_all` heartbeat timeouts

**Symptom.**
```
(deterministic) timeout at `simp`, maximum number of heartbeats
(200000) has been reached
```
Aristotle's proofs sometimes wire `simp_all +decide [list1, list2, ...]`
through three or four nested branches. Each layer multiplies the search.

**Fix.** Either `set_option maxHeartbeats 400000` locally, or split the
chain. Splitting is preferred: it's a signal that the proof is doing
too much in one tactic.

## Gotcha 5 — `COMPLETE_WITH_ERRORS` is usually fine

**Symptom.** Aristotle returns project status `COMPLETE_WITH_ERRORS`
even though every target sorry was closed cleanly (e.g. round 1,
project be7c0245).

**Fix.** *Don't trust the status; build the integrated tarball.* Our
recipe (`scripts/aristotle-integrate.sh`) extracts to a sandbox and
runs `lake build` on the patched repo before deciding whether to
commit. If `lake build` succeeds and only expected sorries remain,
the integration is sound regardless of the status flag.

**Why this happens.** Aristotle's status reflects internal verification
issues that don't necessarily invalidate the output. Aristotle's
`ARISTOTLE_SUMMARY.md` is the more useful signal.

## Gotcha 6 — `admit` is `sorry` in Lean 4 (not a sed trick)

**Symptom.** A natural attempt to narrow Aristotle's scope is to
`sed -i 's/sorry/admit/' BlockSynchroniser/**/*.lean` for *non-target*
files, hoping Aristotle will see no sorries to chase except the ones
you want. Doesn't work: Lean 4 maps `admit` to `sorry`, so Aristotle
treats them identically.

**Fix.** Use *targeted prompts* instead. Name the specific theorems
("prove `lemma3_honest_not_blamed`, `lemma4_round_latency_delta`,
`lemma5_round_latency_or_blamed` in PerformanceLemmas.lean — leave
all other sorries unchanged"). This is the Aristotle-native scope
mechanism.

## Gotcha 7 — tarball state is at submission time

**Symptom.** You submit at T₀, then at T₁ make local edits to other
files, then Aristotle returns at T₂. The tarball reflects the repo
*as of T₀*, not T₂. Naively `cp -r` from the tarball will silently
revert your T₁ edits.

**Fix.** *Diff narrowly.* Only copy the target files Aristotle was
asked to modify. Anything else in the diff is your local progress
and must be preserved.

In the integration script, we explicitly select only the prompted
target files; everything else in the tarball is read-only reference.

## Gotcha 8 — file-freezing is not optional

**Symptom.** You edit a file Aristotle is currently working on. Either
(a) Aristotle's resulting proofs reference your *old* statements and
no longer typecheck after merge, or (b) the merge produces structurally
plausible-looking code that's subtly inconsistent.

**Fix.** Track in-flight files in
[`docs/aristotle-projects.md`](aristotle-projects.md) and refuse to
edit anything in the *frozen-files* union. Run `aristotle cancel <id>`
if a file becomes urgent.

We've run up to 7 concurrent submissions under this rule. The disjoint-
files invariant is what makes that safe.

## Gotcha 9 — bundle fixes before resubmitting

**Symptom.** Aristotle returns `COMPLETE_WITH_ERRORS` with N residual
sorries. Tempting to fix one, resubmit, and let it close the rest.

**Fix.** Diagnose *all* residuals first; categorize each as

1. **Tactical-wall continuation** — needs more Mathlib lemma hints,
2. **Semantic gap** — definition doesn't satisfy the spec; revise,
3. **Missing well-formedness invariant** — add the hypothesis.

Then bundle fixes and resubmit *once*. Each round is ~1h wall-clock;
unbundled iteration is the most expensive thing you can do.

## Gotcha 10 — reset incomplete proofs before resubmitting

**Symptom.** A previous round returned a structural proof that doesn't
quite work; you've since changed the theorem statement to fix the
semantic gap. The structural shape is now stale. If you leave it in,
Aristotle anchors on it instead of restarting the search.

**Fix.** Before resubmitting, delete Aristotle's prior proof body and
reset to a plain `:= by sorry`. The slate is clean; Aristotle re-plans
against the new statement.

## Gotcha 11 — Aristotle invents helper modules

**Symptom.** Round 3e returned not just a modified `PerformanceLemmas.lean`
but also a *brand new* module `StepPreservation.lean` that didn't exist
before. `lake build` fails because the root library doesn't import it.

**Fix.** Inspect the tarball's full file list (`tar tzf`); if a new
module appears, add it to `BlockSynchroniser.lean` (root re-export
file) before building. This is also a signal that Aristotle saw a
factoring opportunity worth keeping.

## Gotcha 12 — Aristotle adds hypotheses to your theorem statements

**Symptom.** You ask Aristotle to prove `lemma4_round_latency_delta`
with a fixed signature; the returned proof works, but the theorem now
takes an extra parameter `(h_lt : LatencyTriangle system time)` you
didn't ask for.

**Fix.** This is *usually* the right call — Aristotle is signaling
that the existing hypotheses don't suffice. Decide:

1. The hypothesis is paper-faithful (e.g. paper Assumption 1 made
   explicit) → keep it, document in the file's docstring, propagate
   to callers.
2. The hypothesis is a Lean-plumbing convenience (e.g. a decidability
   instance) → keep it, mark as boilerplate.
3. The hypothesis weakens the theorem → reject; tighten the prompt
   ("do not weaken the statement; if you cannot prove it as stated,
   say so").

In round 3e, `LatencyTriangle` was case (1): paper Assumption 1, made
explicit. Worth keeping.

## Gotcha 13 — provenance markers earn their keep at integration time

**Convention.** Every Aristotle-filled proof gets a comment line:
```
-- proof: aristotle (project <8-char-prefix>)
```
immediately above the theorem (or above the helper-section header).

**Why this matters.** Six months later, you're deciding whether to
hand-rewrite a proof for clarity. `git blame` tells you "this line
came from commit `6d93990`"; the provenance marker tells you *which
project ID*, which lets you find the prompt and the original tarball.
Without markers, this archaeology is hopeless.

It also makes `grep -r "proof: aristotle"` an instant audit
("how many of our proofs are AI-generated?") — a question the eventual
final report needs to answer precisely.

## Gotcha 14 — wall-clock economics favor concurrency

**Observation.** A single Aristotle round costs ~1h wall-clock
(varies, but order-of-magnitude). Serialized iteration of N rounds
costs ~Nh. Concurrent submission of N rounds (under the file-disjoint
freezing rule) costs ~1h *total* — the ratio is the dominant
productivity multiplier.

**The math.** During a 1h round, the human is reading the paper,
hand-proving short lemmas, fixing definitions. With one in-flight
round, that work fills the wait time well. With seven, the work is
*sliced finer* (each free file gets a smaller human window) but no
single round is the bottleneck.

**The cost.** Bookkeeping. The file-freezing rule has to be
mechanically enforced or you lose work. We use
[`docs/aristotle-projects.md`](aristotle-projects.md) as the single
source of truth for the frozen-files set; CLAUDE.md tells the next
session to check it on startup.

## Gotcha 15 — `PROVIDED SOLUTION` docstrings work

**Observation.** When the theorem's docstring contains a paper-style
proof sketch labeled `PROVIDED SOLUTION`, Aristotle's success rate
(measured loosely, by "did the proof go through on the first round")
is noticeably higher.

**Hypothesis.** The sketch acts as a strong prior on which Mathlib
lemma family to search. Without it, Aristotle's search has to
re-derive the strategy from the goal alone.

**Practice.** For any theorem with a non-trivial paper proof, transcribe
the paper sketch into the docstring before submitting. This is also
useful documentation regardless of whether Aristotle is involved.

## Gotcha 16 — the SUMMARY.md lies (sometimes)

**Symptom.** Aristotle's `ARISTOTLE_SUMMARY.md` confidently states
"All proofs compile and use only standard axioms." `lake build` then
fails with multiple errors in the very file the summary mentions.

**Fix.** Always run `lake build` against the integrated tarball
before trusting the summary. The summary describes Aristotle's
*intent* (and possibly its internal verification result against
slightly different Mathlib state); the local build is ground truth.

In round 3e, the summary said all helpers compile; the actual
result had `exact?` placeholders and `▸` mismatches. The summary
was directionally correct (proofs *would* compile after small fixes)
but not literally correct.

**Generalization.** Treat any agent's claim about its own output as
a hypothesis to verify, not a fact. This applies to Aristotle, to
Claude, to any future tool — the cost of verifying is small, the
cost of trusting blindly compounds.

## Gotcha 17 — round numbering is fluid

**Practice.** Round numbers (1, 2, 3a, 3b, 3e, 3e-followup, 4, 5, 6)
emerged organically — we didn't pre-allocate them. Subletters (`a`/`b`
/...) appear when one logical round splits across files; followups
(`-followup`) appear when a round leaves residual sorries we want to
close.

The numbering exists for *human navigability* in the project tracker
and changelog, not for any tool. Don't over-formalize it; renumber
freely if it helps clarity.

## Gotcha 18 — Aristotle's structural decomposition is reusable even if proofs aren't

**Observation.** Round 3d returned 5 main Mysticeti liveness theorems
sorry-free at the top level, *delegating* to 11 helper lemmas left
as `sorry`. The top-level proofs are just the algebraic glue;
the math is in the helpers.

**Why this is good.** The decomposition is itself worth committing.
A subsequent round can attack the helpers in parallel (each is small
and self-contained), and the top-level theorems already give the
user a meaningful "consensus_liveness" theorem to inspect — they
just rely on assumptions that need to be discharged later.

**Why it's a little bad.** A naive sorry-counter sees 11 sorries
and reports the file as "barely started." A theorem-counter sees
5 main theorems closed. Both are right. We track both in
[formalization-status.md](formalization-status.md).

## Gotcha 19 — strip the word "sorry" from prose during integration

**Symptom.** Aristotle's docstrings sometimes mention "remaining
`sorry` proofs" or "stubbed with `sorry`" in prose. Even when those
sentences are *describing* the proof obligation correctly, the
literal token pollutes `grep -rn 'sorry'`.

**Fix.** Search-and-replace `sorry` → `stub`/`pending`/`incomplete`
in any non-tactic position during integration. We do this manually
because the grep-driven sorry-count is a load-bearing metric for the
project's status report.

## Gotcha 20 — `set_option` overrides leak

**Symptom.** Aristotle sometimes sprinkles `set_option maxHeartbeats N`
or `set_option synthInstance.maxHeartbeats N` to push proofs
through tight tactical chains. These persist in the file and silently
slow every subsequent build.

**Fix.** When integrating, scan for `set_option` lines that weren't
in the original. If they're working around a real timeout, decide
whether to (a) accept the cost, (b) refactor the proof to avoid it,
or (c) restrict the override scope with a `section ... end` block.

We've kept `set_option` cases case-by-case; never globally.

## What we'd put in a blog post

The operational thesis: **the math tactical wall and integration
gotchas are two faces of the same coin.** Aristotle delegates the
wall well; the gotchas are the cost of integration. Both are
predictable and both have repeatable fixes. A workflow that takes
both seriously — frozen files, narrow imports, build-the-tarball
verification, bundled iteration — turns Aristotle from "occasional
useful black box" into "reliable proof microservice."

Concrete worked examples we can ground the post in:

- Round 1 (be7c0245, Validation.lean): clean win, 4 theorems closed,
  `import Mathlib` narrowing was the only edit. The "easy mode" case.
- Round 3c/3d (Mysticeti Safety/Liveness): structural delegation —
  main theorems sorry-free at top, helper lemmas left for a later
  round. Decomposition pattern.
- Round 3e (PerformanceLemmas + StepPreservation): full inventory —
  `import Mathlib`, `exact?`, `▸`, new helper module, partial closure.
  The "every gotcha at once" case.
- Round 4 / R5 / R6 / R3a / R3b: live as of writing — outcomes will
  give us either confirming or surprising data.

Counter-example: realizability lemmas in `Validation.lean`
(hand-proved): the math content was the work, no Mathlib idiom would
have helped. Tactical wall delegation would be premature; this is the
"content gap" side of the wall/gap dichotomy from the companion seed.

## Cross-references

- [math-tactical-wall.md](math-tactical-wall.md) — conceptual companion (wall vs gap)
- [aristotle-workflow.md](aristotle-workflow.md) — operational manual (submit → integrate → verify)
- [aristotle-attributions.md](aristotle-attributions.md) — per-project receipts (concrete grounding for each gotcha)
- [aristotle-projects.md](aristotle-projects.md) — live frozen-files / in-flight state
- [scripts/aristotle-integrate.sh](../scripts/aristotle-integrate.sh) — the integration helper that automates several of these checks

## TODO before publishing

- Resolve the in-flight rounds and cite results (which gotchas
  recurred, which were one-offs).
- Quantify: how many rounds total, how many `COMPLETE_WITH_ERRORS`
  with sound output, how many *actual* failures, total wall-clock time
  vs total CPU/credits.
- Decide whether to include the integration script verbatim or
  abstracted. Probably abstracted, with a link to the repo for the
  curious.
