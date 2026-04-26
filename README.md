# BlockSynchroniser

A Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

> 📖 **Start here: [formalization.md](formalization.md)** — overview of what we're
> building, the repository layout, the distinction between paper theorems and
> validation lemmas, and pointers to the deeper docs.
>
> 📝 **Paper feedback: [docs/mechanization-findings.md](docs/mechanization-findings.md)** —
> running log, in paper terminology only, of issues the formalization
> surfaced about the Beluga paper (missing assumptions, scope ambiguities,
> implicit invariants). This is the working list of edits we plan to
> propose to the paper authors.

## What this is

A formal model of a block synchronizer for BFT consensus: validators
collectively build a structured, ever-growing set of blocks while tolerating
up to `f` Byzantine validators out of `n ≥ 3f + 1`. The four properties of
Definition 1 (Round-Progression, Round-Termination, Block availability,
Causal availability) are the load-bearing definitions; the rest of the
formalization either supports them, validates them, or proves the Beluga
protocol satisfies them.

## Build

```bash
lake update
lake build
```

Requires Lean 4 toolchain `leanprover/lean4:v4.28.0` (pinned in
[`lean-toolchain`](lean-toolchain)). The `lake update` step pulls Mathlib
and Batteries; the `lake build` step uses Mathlib's cloud cache to avoid
recompiling Mathlib from scratch.

## Documentation map

The project produces three deliverables alongside the Lean code itself:

1. **Paper feedback** — observations the formalization surfaced
   about the Beluga paper, packaged for the paper authors.
2. **Final report** — written record of what was formalized, what
   was left open, and what we learned about the proof structure.
3. **Two blog seeds** — public-facing write-ups about (a) when to
   delegate Lean proofs and (b) what integrating an LLM prover into
   a real Lean repository actually costs.

The documents below feed into one or more of those deliverables.
Each entry says *what the document contains*, *who reads it*, *when
to consult it*, and *what end-product it informs*.

### For the paper authors

| Document | What it is |
|---|---|
| [docs/mechanization-findings.md](docs/mechanization-findings.md) | **Running log of paper-side observations from the formalization.** Each finding (`F-1` … `F-11`, plus sub-findings like `F-1a`) has severity, category, affected paper sections, headline issue, recommended action, and our Lean-side address. **Audience:** paper authors, ourselves when proposing edits. **Use when:** mechanization surfaces a paper concern (missing assumption, hidden invariant, off-by-one, scope ambiguity). **Feeds:** paper feedback — direct list of edits to propose. Paper terminology only; no Lean. |
| [docs/paper-feedback-l1-l2-fairness.md](docs/paper-feedback-l1-l2-fairness.md) | Standalone deep dive on finding **F-1** (scheduler fairness for Lemmas 1 & 2). **Audience:** anyone who wants the longer counterexample-and-fix narrative for F-1 without the table-format constraint. **Use when:** F-1 needs to be defended in a discussion with the authors. **Feeds:** paper feedback (companion to the F-1 row in mechanization-findings.md). |
| [docs/Block_Sync_Project.pdf](docs/Block_Sync_Project.pdf) | The paper itself. The source of truth for paper terminology and statements. |

### Project overview

| Document | What it is |
|---|---|
| [formalization.md](formalization.md) | **Project-wide overview and the canonical paper→code map.** Three things live here: (1) a per-paper-section table mapping every paper definition / lemma / theorem to its Lean home and current proof status (`✅` / `◐` / `☐` / `⊘` / `⏸`); (2) Lean-side modeling notes that explain non-paper-relevant decomposition choices; (3) the **"Refinement chain and reusable trace invariants"** section explaining the proof architecture (executable→spec refinement closure, the `BlockInv` / `AcceptInv` / `CausallyClosed` vocabulary). **Audience:** anyone trying to understand the proof structure or check paper conformance. **Use when:** orienting before a session, deciding what to delegate, checking the scope of a specific paper item. **Feeds:** final report's "what we built" section. |
| [docs/formalization-plan.md](docs/formalization-plan.md) | The original phased plan: which subsystems land in which phase, the order in which paper sections were tackled, the scope decisions we made up-front. **Audience:** anyone reconstructing how we chose what to do. **Use when:** the question is "why was X done before Y?" or "why is Z out of scope?". **Feeds:** final report's project-history narrative. Mostly stable now (the plan was executed). |
| [docs/final-report-outline.md](docs/final-report-outline.md) | Skeleton of the eventual final report. Section headings + intended content but not the prose itself. **Audience:** ourselves at the end of the project. **Use when:** writing the report. **Feeds:** the report itself. |

### Aristotle workflow & process

These four documents track the *delegation* side of the proof effort
(Aristotle is Harmonic's LLM theorem prover for Lean).

| Document | What it is |
|---|---|
| [docs/aristotle-workflow.md](docs/aristotle-workflow.md) | **Operational manual** for the Aristotle delegation cycle: prompt construction, the iteration loop (categorizing remaining sorries after `COMPLETE_WITH_ERRORS`), file-freezing rules, integration recipe, scope-discipline lessons. **Audience:** anyone running an Aristotle round. **Use when:** preparing a submission or diagnosing why a round stalled. **Feeds:** the *operational* blog seed (`blog-aristotle-integration-gotchas.md`). |
| [docs/aristotle-projects.md](docs/aristotle-projects.md) | **Live tracker** of submissions: `Active` (in flight, with frozen files), `Queued` (planned), `Completed` (status, target theorems, integration commit). Updated on every state change. **Audience:** the next session, the current session checking concurrency. **Use when:** at session start (what's frozen?), after a result returns (what's next?). **Feeds:** the eventual round-by-round timeline in the final report. |
| [docs/aristotle-attributions.md](docs/aristotle-attributions.md) | **Per-project full attribution log** — for each completed Aristotle round: theorems closed, helper lemmas added, signature changes, side effects, verifier confirmation, notes on what made the round succeed/fail. Long-form; one section per project ID. **Audience:** ourselves for the final report; reviewers wanting to know which proofs are LLM-derived. **Use when:** integrating a returned result. **Feeds:** the per-proof provenance section of the final report. |
| [docs/math-tactical-wall.md](docs/math-tactical-wall.md) | **Conceptual seed** for the wall-vs-gap idea: most Lean delegation pain isn't math, it's *Lean plumbing past the math tactical wall* (Mathlib lemma discovery, idiomatic tactic chaining, type-class disambiguation). **Audience:** Lean users deciding when delegation pays off. **Use when:** justifying why we delegate certain proofs and not others. **Feeds:** the *conceptual* blog post. |
| [docs/blog-aristotle-integration-gotchas.md](docs/blog-aristotle-integration-gotchas.md) | **Operational seed**: 21+ concrete gotchas hit when integrating Aristotle output into a real Lean repo (`import Mathlib` linker blowups, `▸` cast mismatches, file-freezing, bundle-then-delegate, etc.). Companion to the wall doc. **Audience:** practitioners adopting an LLM prover. **Use when:** a new gotcha is observed (append it). **Feeds:** the *operational* blog post. |

### Per-finding paper-side documents

| Document | What it is |
|---|---|
| [docs/mechanization-findings.md](docs/mechanization-findings.md) | (See above — the index of findings.) |
| [docs/paper-feedback-l1-l2-fairness.md](docs/paper-feedback-l1-l2-fairness.md) | (See above — F-1 deep dive.) |

Other findings get long-form treatment by appending to
`mechanization-findings.md`'s narrative section. New
`docs/paper-feedback-<topic>.md` files are created only for
findings substantial enough to want a self-contained companion
write-up (currently just F-1; F-7 is a candidate when restatement
is taken up).

### History & per-session record

| Document | What it is |
|---|---|
| [changelogs/](changelogs/) | **Per-stage timestamped changelogs** — one file per phase / sub-phase / Aristotle integration. Each entry covers what changed, why, build state (jobs, sorries), Aristotle attributions (project IDs), what's next. The hard rule from `CLAUDE.md`: every commit that lands a phase / integration / definition repair / discovery is paired with a changelog entry. **Audience:** the next session, the final-report writer. **Use when:** picking up after compaction or wanting to know why a definition has its current shape. **Feeds:** the project-timeline portion of the final report. |
| [changelogs/2026-04-25-session-narrative.md](changelogs/2026-04-25-session-narrative.md) | **Cross-phase decision threads** spanning multiple commits — a separate file because the per-session changelogs alone don't capture decisions that take more than one commit to play out. **Audience:** ourselves later. **Use when:** documenting a decision that spans several days of work. **Feeds:** the final report's narrative voice (rather than its tables). |
| [changelogs/README.md](changelogs/README.md) | Long-form conventions for the changelog directory. **Audience:** the changelog author. **Use when:** unsure how to name or scope a changelog entry. |

### Project guidance for AI assistants

| Document | What it is |
|---|---|
| [CLAUDE.md](CLAUDE.md) | **Startup brief**: the operational state, the two-track workflow (hand-prove + Aristotle delegation), file-freezing rules, sorry-comment hygiene, doc-update obligations after every proof round. Read on every session start and after compaction. **Audience:** Claude. **Feeds:** session-startup behavior, not the report. |

## Project structure

```
block-sync-lean/
├── BlockSynchroniser/          # Library modules (per-concept files)
├── Main.lean                   # Driver (executable Beluga lands in Phase 4)
├── docs/                       # Plan, status, workflow notes; the paper
├── changelogs/                 # Per-stage changelogs
├── formalization.md            # Overview & entry point
└── README.md                   # This file
```

See [formalization.md](formalization.md#repository-layout) for the per-file
breakdown.

## License

Apache License, Version 2.0 — see [LICENSE](LICENSE).
