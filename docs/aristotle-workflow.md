# Aristotle Workflow Notes

Self-note for Claude. Operating manual for delegating proofs to Aristotle (Harmonic's Lean-4 theorem-proving agent).

## What it is

Aristotle is a Lean-4 reasoning agent. It can:
1. **Fill `sorry`s** in a Lean project — submit project, get back filled proofs.
2. **Formalize from natural language** — submit `.tex`/`.md`/`.txt`, get back Lean.
3. **Disprove false statements** and produce counterexamples (uses an auto-injected `negate_state` tactic).

It runs on a fixed toolchain: **Lean `v4.28.0`** and **Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`** — the same commit our project is pinned to. Compatibility is perfect for this repo.

## Setup (already done)

- CLI installed at `/Users/ilyasergey/.local/bin/aristotle` (version `aristotlelib 1.0.1`)
- `ARISTOTLE_API_KEY` exported in `~/.zshrc`
- `aristotle list` works → authenticated

## The two commands we'll use

### Submit a Lean project to fill sorries
```
aristotle submit "<prompt>" --project-dir . --wait
```
- Tarballs the directory (skips `.olean` and `.lake/packages/`).
- `--wait` blocks with a live progress display; otherwise returns a project ID.
- 100 MB per-file limit (irrelevant for us).
- Output is a `.tar.gz` with the filled-in project.

### Manage projects
```
aristotle list                              # most recent
aristotle list --status COMPLETE IN_PROGRESS
aristotle result <id> --destination out.tar.gz
aristotle result <id> --wait --destination out.tar.gz   # wait then download
aristotle cancel <id>
```

Project statuses: `QUEUED`, `IN_PROGRESS`, `COMPLETE`, `COMPLETE_WITH_ERRORS`, `OUT_OF_BUDGET`, `FAILED`, `CANCELED`.

## Hard rules from the docs

- **Aristotle does not modify definitions by default.** A `def foo : Nat := by sorry` stays untouched — `sorry` is treated as opaque data, not a proof obligation. Only `theorem`/`lemma`/`example` `sorry`s get filled.
- **Aristotle does not see comments inside `by` blocks.** Hints belong in the docstring above the theorem.
- To give a proof sketch, prefix the theorem with a docstring containing a `PROVIDED SOLUTION` block:
  ```
  /--
  Statement of theorem in natural language.

  PROVIDED SOLUTION
  Sketch of the proof in prose. As detailed or general as needed.
  -/
  theorem foo : … := by sorry
  ```
- **Project structure required**: `lakefile.toml` or `lakefile.lean`, `lean-toolchain`, properly-importing `.lean` files. We have all three.

## Our workflow for proofs

For every theorem we want proved, the procedure is:

1. **State it precisely** with `:= by sorry` in the right file.
2. **Verify it elaborates** (`lake build` succeeds with the `sorry` in place). Aristotle works best on skeletons that already typecheck modulo `sorry`.
3. **Try the proof manually first** if it looks tractable (one to two screen lines). Saves a round trip.
4. **If hard**, write a `PROVIDED SOLUTION` docstring with the paper's proof sketch (Beluga's lemmas have proofs in §5 and Appendix D — copy them in prose).
5. **Commit current state** to a feature branch before submitting. Aristotle's response replaces files; we want a clean diff to review.
6. **Submit**: `aristotle submit "Fill in the sorries" --project-dir . --wait`. (For broader work: "Build auxiliary lemmas that would help prove the main sorry'd goal" or one of the cookbook prompts below.)
7. **Extract the result tarball** to a temp directory, diff against the working copy, review carefully, then apply.
8. **Verify** the filled-in proof actually builds: `lake build`. Don't trust the `COMPLETE` status alone.

## Cookbook prompts (from docs)

- `"Fill in all the sorries in this project"` — default workhorse.
- `"Prove this using only `ring` and `omega`, avoiding heavy automation"` — when we want a readable proof.
- `"Build auxiliary lemmas that would help prove the main sorry'd goal in this file"` — when the gap is too big for one shot.
- `"Develop API lemmas for the main structure in this file: coercions, simp lemmas, and basic properties"` — for new structures.
- `"Build a formal sorry'd skeleton closely following my paper, with theorem statements matching each result"` — useful if we ever want to bulk-formalize from a `.tex`.
- `"Refactor this file into a modular structure: extract helper lemmas, group related definitions, and minimize imports"` — code quality pass.
- `"Golf all the proofs in this project: minimize tactic count and simplify where possible"` — final pass.

## Resuming `OUT_OF_BUDGET` projects

```
aristotle result <id> --destination partial.tar.gz
mkdir partial-output && tar -xzf partial.tar.gz -C partial-output
aristotle submit "Fill in the sorries" --project-dir ./partial-output --wait
```

## Division of labor — what to delegate vs. do ourselves

**Do ourselves (don't delegate):**
- All definitions, structures, typeclasses (Aristotle won't change them anyway).
- The four properties of Definition 1 — phrasing matters, must match paper exactly.
- Validation/non-vacuity scaffolding (`goldenTrace`, realizability lemmas).
- Trivial proofs (`rfl`, `simp`, `decide`, one-line `omega`).
- Quorum-intersection lemma (it's the load-bearing tool — better understood explicitly).

**Delegate to Aristotle:**
- Lemma 10 (pigeonhole on round-robin schedule) — pure combinatorics.
- Lemmas 13–15 (Mysticeti-Beluga safety building blocks) — quorum-intersection chains.
- Lemma 16 + Theorem 7 (consensus safety) — backward induction.
- Block-availability / causal-availability theorems (T1, T2) — once the protocol relation is in place.
- Any auxiliary list/finite-set lemmas we don't want to write.

**Hybrid (maybe try both):**
- Lemma 1 (3Δ round entry after GST) — try by hand, fall back to Aristotle with a `PROVIDED SOLUTION` from §5.
- Lemma 2 — same.
- Theorems 3, 4 (Round-Progression, Round-Termination) — start with Aristotle on a sketch, refine.

## Engagement rules

- **One task per submission.** Don't bundle "fill all sorries" with "refactor everything." The cookbook prompts are mutually exclusive.
- **Branch hygiene.** Always submit from a clean branch with all work committed. Tarball reflects the current state.
- **Read every diff.** `COMPLETE` means Aristotle's verifier accepted; it doesn't mean the proof matches our intent or that it's the proof we want maintained long-term.
- **Re-build after applying.** `lake build` is the ground truth.
- **Cost awareness.** Each submission costs budget. Don't poll cheaply — write a good prompt, wait, review.

## Reference

- Docs (auth-gated, in PDFs under [docs/aristotle/](aristotle/)).
- Dashboard: <https://aristotle.harmonic.fun>.
- Lean toolchain: `leanprover/lean4:v4.28.0`.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
