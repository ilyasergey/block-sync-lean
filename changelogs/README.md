# Changelogs

Per-stage and meta-narrative entries for this formalization. Each entry is
a `YYYY-MM-DD-<scope>.md` file, oldest first (alphabetic sort).

## How to read

| Entry pattern | Purpose |
|---|---|
| `…-phase-N-<topic>.md` | Per-phase: what changed in code, build status, Aristotle-attributed proofs, status delta, next stage. |
| `…-phase-N-partial-<topic>.md` | Sub-phase entry when a phase is split across multiple commits. |
| `…-session-narrative.md` | Meta-changelog capturing decisions and threads that span multiple commits — *why* choices were made, what was considered and abandoned, conversational context. |
| `…-discussion-<topic>.md` | (Future) topic-scoped discussion thread (e.g., `discussion-veil-assessment.md`) — used when a substantial decision deserves its own file rather than fitting into a phase entry. |
| `…-planning-and-aristotle-setup.md` | Initial bootstrap. |

## Conventions

- Code-level commits get phase-level entries on the same day (or batched
  if multiple sub-phase commits land together).
- Decisions that span phases — e.g., "should we use Veil?" — get either
  a section in the relevant phase entry or a standalone narrative entry.
- Aristotle work is tracked in two places: granular per-project state in
  [`docs/aristotle-projects.md`](../docs/aristotle-projects.md), and
  per-phase summary in the phase changelog ("Aristotle work this stage").
- Each entry lists `lake build` job count and remaining `sorry` count at
  end of stage so the build trajectory is visible.

## Reconstructing the conversation

The narrative entries (`…-session-narrative.md`) are the place to look
for "*why* did we end up here?" questions. Phase entries are sufficient
for "*what* changed when?" but light on rationale.
