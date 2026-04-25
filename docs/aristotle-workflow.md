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

## Operational recipe (concrete)

Use this for every Aristotle round-trip.

### 1. Prepare

- Theorem stated with `:= by sorry` in the right file. The file has a docstring `PROVIDED SOLUTION` block above it (paper's proof sketch in prose if available).
- `lake build` succeeds with the `sorry` in place. Aristotle works best on skeletons that already typecheck modulo `sorry`.
- Working tree committed on a feature branch (e.g. `aristotle/<theorem-name>`). The tarball reflects the current state, so commits before submission keep the diff reviewable.

### 2. Submit

```bash
TS=$(date +%Y%m%d-%H%M)
aristotle submit "Fill in the sorries" \
  --project-dir . \
  --wait \
  --destination /tmp/aristotle-$TS.tar.gz
```

`--wait` blocks with a live progress display. Without `--wait` it returns a project ID; check later with `aristotle result <id> --wait --destination ...`.

For non-`fill-sorries` work see the **Cookbook prompts** section below.

### 3. Extract to a sandbox (never overwrite the working tree directly)

```bash
SANDBOX=/tmp/aristotle-out-$TS
rm -rf "$SANDBOX" && mkdir -p "$SANDBOX"
tar -xzf /tmp/aristotle-$TS.tar.gz -C "$SANDBOX"
```

### 4. Diff to find changed files

```bash
diff -rq BlockSynchroniser "$SANDBOX/BlockSynchroniser"
```

Aristotle should only change files containing the `sorry`s. Anything else is a red flag.

### 5. Read the actual hunks

```bash
diff -u BlockSynchroniser/<file>.lean "$SANDBOX/BlockSynchroniser/<file>.lean" > /tmp/aristotle-$TS.diff
less /tmp/aristotle-$TS.diff
```

Three checks per filled-in proof:

- Does it match the `PROVIDED SOLUTION` sketch (or a reasonable proof of the same shape)?
- Tactics readable, or an opaque automation chain?
- Any residual `sorry`/`admit` left behind?

### 6. Apply surgically

Two options:

```bash
# Option A — wholesale file copy (when the entire file diff is acceptable)
cp "$SANDBOX/BlockSynchroniser/<file>.lean" BlockSynchroniser/<file>.lean

# Option B — patch (cherry-pick hunks)
git apply /tmp/aristotle-$TS.diff           # all hunks
git apply --reject /tmp/aristotle-$TS.diff  # keep working state on conflict
```

### 7. Verify

```bash
lake build
```

`COMPLETE` from Aristotle is a *claim*, not proof. `lake build` is the ground truth.

If a `sorry` remains: Aristotle gave up partway. Use the `OUT_OF_BUDGET` resume recipe below.

### 8. Annotate and commit

Before committing, add a one-line marker above each filled proof so `git blame`
and grep both find provenance:

```
-- proof filled by Aristotle (project <id>)
```

Commit message form:

```
phase X.Y: <theorem-names> proofs (filled by Aristotle, project <id>)
```

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

## Delegation policy (token-aware, concurrency-aware)

Default to delegation. Hand-proofs cost my context tokens; Aristotle costs API
budget. Tokens are scarcer than budget right now, so the bias is **delegate
unless the proof is one or two lines.**

### Attempt budget per proof

A *small* hand-attempt limit, not exhaustive search:

| Proof shape | Hand budget | Then |
|---|---|---|
| One-liner: `rfl`, `decide`, `simp`, `omega` | always try first | move on |
| Short tactical (≤ ~10 lines, no induction) | 1 attempt, ≤ 5 min | delegate |
| Medium (induction or list arithmetic) | sketch only; if not green in 5 min | delegate |
| Anything bigger | delegate immediately with a `PROVIDED SOLUTION` |

If I find myself iterating on tactic minutiae or grepping Mathlib for the
right `simp` lemma, that's the cue to delegate — I am the wrong tool for
that work.

### Concurrency rule (avoid file conflicts)

When I delegate, I keep working — but **not on files Aristotle is touching.**
Concretely:

- Before submitting, decide which files Aristotle will modify (the ones with the
  `sorry`s I'm asking it to fill). These files are *frozen* on my side until
  the result is integrated.
- I work on a *different* set of files in parallel. Common patterns:
  - Aristotle proves `golden_*` in `Validation.lean`; I write `Beluga/Patterns.lean` simultaneously.
  - Aristotle fills auxiliary list lemmas in a helper file; I sketch the next-phase definitions.
- When the result returns, I integrate it (steps 3–8 of the operational recipe), then unfreeze that file.
- If I have to touch a frozen file urgently (definitional bug discovered),
  I cancel the project (`aristotle cancel <id>`) rather than risk a merge mess.

### Batch when possible

Submitting one project that fills five `sorry`s costs roughly the same
round-trip as submitting one for one `sorry`. If multiple sorries cluster
in non-frozen files and don't depend on each other, batch them into a
single submission.

### What I still do myself

- All definitions, structures, typeclasses (Aristotle won't change them anyway — `def := by sorry` is opaque to it).
- The four properties of Definition 1 — phrasing must match paper exactly; phrasing changes invalidate downstream proofs.
- Validation scaffolding (`goldenTrace`, `realizable_*`, anti-witness traces).
- The quorum-intersection lemma — load-bearing for everything, worth understanding explicitly.
- One-liners (`rfl`, `simp`, `decide`, `omega`).
- Final review of every Aristotle-filled proof and the diff.

### What I delegate by default

- `golden_*` satisfaction theorems (computational; tedious).
- Lemma 10 (round-robin pigeonhole).
- Lemmas 13–15 (quorum-intersection chains).
- Lemma 16 + Theorem 7 (backward induction over rounds).
- Theorems 1, 2 (block / causal availability) — once the protocol relation is in place.
- Auxiliary list/Finset lemmas I don't want to write.
- Anything where the paper has a multi-step prose proof I can paste verbatim into a `PROVIDED SOLUTION`.

### Hybrid (attempt → delegate fallback)

- Lemma 1 (3Δ round entry after GST) — try a sketch (≤ 30 min), fall back with `PROVIDED SOLUTION` from §5.
- Lemma 2 — same.
- Theorems 3, 4 (Round-Progression, Round-Termination) — try by hand briefly, then delegate with the paper's argument as the sketch.

## Engagement rules (tight)

- **One task per submission.** Don't bundle "fill all sorries" with "refactor everything."
- **Branch hygiene.** Submit from a clean, committed feature branch (`aristotle/<scope>`).
- **Frozen files.** Never edit a file currently under an in-flight Aristotle submission. Cancel the project if you must.
- **Read every diff.** `COMPLETE` is a claim; the diff is the proof.
- **Re-build after applying.** `lake build` is the ground truth.
- **Annotate provenance.** Every Aristotle-filled proof carries `-- proof filled by Aristotle (project <id>)` and the commit message names the project ID.
- **Acknowledge in chat.** When a proof returns from Aristotle, surface it: which theorem, project ID, hand vs. delegated, anything I'd flag in the diff.
- **Cost awareness.** Each submission costs API budget. Write a good prompt, wait, review — don't churn submissions on the same theorem.

## Project tracking + attribution

Two files:

- [`aristotle-projects.md`](aristotle-projects.md) — single source of
  truth for in-flight / queued / completed projects. Update on every
  submission and completion.
- [`aristotle-attributions.md`](aristotle-attributions.md) — audit
  trail of *what was proved by Aristotle*, with paper origins, helper
  lemmas, integration commit, side-effects on the project. **This is
  the source of attribution for the final report.** Append a new
  section per completed project.

## Provenance markers in source

Every Aristotle-filled proof carries this comment immediately above its
declaration:

```
-- proof: aristotle (project <id-prefix>)
theorem foo : … := by …
```

`<id-prefix>` is the first segment of the project UUID (e.g.
`be7c0245`). This makes:

- `git blame` answer "who proved this" without diff archaeology;
- `grep -r "proof: aristotle" BlockSynchroniser/` enumerate every
  AI-attributed proof;
- code review unambiguous.

Helper lemmas added by Aristotle (in support of a target theorem) get
the same marker if they're substantive; trivial one-liners may share a
marker on the section header.

## Submission tip: narrow the scope by `admit`-ing irrelevant sorries

Aristotle's processing time scales with the number of `sorry`s in the
project, since it tries to fill *all* of them. To speed turnaround when
you only want a specific subset proved, **temporarily replace
irrelevant `sorry`s with `admit`** before submission:

```bash
# Snapshot current state
git stash push -m "pre-aristotle-narrowing"

# Replace all sorries you don't want filled
# (regex: `sorry` immediately preceded by `:= by` or `by`, in files
# you do NOT want Aristotle touching)
sed -i '' 's/:= by sorry$/:= by admit/g' BlockSynchroniser/{Quorum.lean,Beluga/Theorems.lean,...}

# Submit — Aristotle now sees only the sorries you care about
aristotle submit "Fill in the sorries" --project-dir . --wait \
  --destination /tmp/aristotle-narrow-$(date +%s).tar.gz

# Restore the original sorries
git stash pop
```

Why this works: `admit` and `sorry` both close any goal, but `admit`
is *not* in Aristotle's filling list (it's understood as "intentionally
left admitted"). After the run, restore the `sorry`s — the proofs
filled by Aristotle for the targeted theorems land in your working
tree, and the `admit`s in untargeted files are reverted by `git stash
pop`.

Caveat: if narrowing causes a definition to be admitted that the
target theorem depends on, Aristotle may fail. Generally safe for
parallel/independent theorems; use carefully for cross-file
dependencies.

## Concept: the math tactical wall

The delegation policy hinges on a recurring pattern we call the *math
tactical wall* — the moment in a proof where the math is clear and only
the Lean plumbing remains. See [math-tactical-wall.md](math-tactical-wall.md)
for the full definition, worked example, and decision cues.

In short: when you find yourself grepping Mathlib for `Finset.card_*`
or trying tactics in sequence (`exact?` / `apply?` / `simp [<random>]`),
you've hit the wall. Aristotle is much better at plumbing than a human
is, so that's the cue to delegate.

## Reference

- Docs (auth-gated, in PDFs under [docs/aristotle/](aristotle/)).
- Dashboard: <https://aristotle.harmonic.fun>.
- Lean toolchain: `leanprover/lean4:v4.28.0`.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
