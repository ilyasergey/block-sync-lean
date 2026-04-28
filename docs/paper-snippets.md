# Paper-ready snippets — Lean formalisation

Drop-in text for the Beluga manuscript, ready to copy verbatim. All
prose is in paper terms; nothing references repository internals.

---

## 1. Contribution line (after current item (3))

(4) We provide a complete machine-checked formalisation of Beluga
in Lean 4 [`\cite{Moura021}`], covering all
non-probabilistic results of the paper — the four block-synchronizer
properties (Definition 1), the §5 main theorems (T1–T4), the
deterministic Appendix C lemmas (L3, L4, L5), and the
Mysticeti-Beluga liveness and safety theorems (T6, T7) along with
their supporting lemmas — discharged from paper-stated assumptions
with no axioms beyond Lean's standard library. The accompanying
material includes the proof artefacts and a paper-to-code map.

## 2. End-of-§5 line

Insert as the last paragraph of §5 (immediately after the proof of
Theorem 4):

All results in this section have been formalised and machine-checked
in Lean 4 [`\cite{Moura021}`]; the proof artefacts are
available with the accompanying material.

## 3. Acknowledgement line

Insert into the Acknowledgements section (replacing or augmenting the
existing acknowledgement):

The Lean 4 formalisation accompanying this paper was developed with
the assistance of Anthropic's Claude Opus 4.7 and Harmonic's
Aristotle [`\cite{aristotle}`].

## 4. Standalone appendix — Lean formalisation

Insert as a new appendix (e.g., Appendix H), self-contained, in paper
terms only.

---

### Appendix H. Lean Formalisation

We provide a complete machine-checked formalisation of the
non-probabilistic results in this paper, developed in Lean 4
[`\cite{Moura021}`]. This appendix records what is
formalised, what is not, and the small number of places where the
formalisation pins down a paper-implicit choice.

#### H.1 What is formalised

- **§2.1 Definitions.** Definition 1 and its four projections —
  Round-Progression (1.1), Round-Termination (1.2), Block-availability
  (1.3), and Causal-availability (1.4) — together with the network
  model, the honest / Byzantine partition, the synchronizer interface
  (`block_propose_i` / `block_accept_i` / `block_store_i`), and the
  causal-history relation.
- **§4 Protocol semantics.** The Beluga protocol of Section 4 is
  modelled in full: block extensions of §4.1, the reputation mechanism
  and admission control of §4.2, the ImPoA-based hybrid pull of §4.3,
  and the §4.4 availability and certificate patterns. The protocol is
  given as both a relational specification and an executable
  step-function that refines it.
- **§5 Main theorems.** Lemma 1 (round-entry within `4Δ`), Theorems 1–4
  (Beluga satisfies block-availability, causal-availability,
  round-progression, and round-termination), and the corollary that
  Beluga is a block synchronizer in the sense of Definition 1.
- **Appendix C deterministic bounds.** Assumption 1 (the latency
  triangle), Lemma 3, Lemma 4, and the deterministic disjunct of
  Lemma 5 ("post-GST round latency `2Δ`-or-blame").
- **Appendix D Mysticeti-Beluga.** The §D.1 consensus rules
  (direct / indirect decision, skip and certificate patterns, the
  round-robin leader schedule), the §D.2 liveness chain
  (L7, L8, the L9 corollary on three consecutive direct commits, L11,
  L12, and Theorem 6), and the §D.3 safety chain
  (L13–L16 and Theorem 7).

The §5 and §D.2 derivations consume only paper-stated assumptions:
the §2 post-GST `Δ`-delivery bound, the §4.2 protocol rules including
the per-action liveness and the timeout `T_{rd} = 5\Delta`, the §4.3
pull mechanism, the §D.1 decision and admission rules, and the §D.3
inherent facts. There are no axioms beyond Lean's standard library.

#### H.2 What is not formalised

The formalisation is restricted to the deterministic content of the
paper. The following items, all of which involve probabilistic or
expected-value reasoning, are out of scope:

- the random-pull complexity bound stated in §4.3 ("each missing
  block can be retrieved in `O(1)` rounds in expectation");
- the expected-latency disjunct of Appendix C Lemma 5;
- Appendix C Lemmas 6 and 7 and Theorem 5 (expected-latency upper
  bounds).

In addition, Appendix D Lemma 11 is mechanised in its existential
form — *post-GST, at every starting round there exists a future
round at which the leader's block is direct-committed* — rather than
in its universal indirect-rule form. The existential form is what
the proof of Theorem 6 actually consumes (Theorem 6 derives every
honest validator's eventual acceptance from §5 in-pool delivery and
§4.2 accept-action liveness, without invoking the indirect-rule
chain). The recursive descent of the §D.1.1 indirect-decision rule
is therefore not mechanised.

#### H.3 Modelling notes

The formalisation pins down two minor choices the paper leaves
implicit; neither weakens or strengthens any paper claim.

- **Block representation.** A block in the paper carries
  `(r, d, author, parents, payload, signature)`. The formalisation
  retains the first five fields and routes Byzantine behaviour
  through the honest / Byzantine partition rather than through
  signature attribution; no theorem we mechanise invokes signature
  semantics.
- **Availability pattern.** §4.4 defines a block as referenced by
  another when the latter strong-links *or* weak-links to it. The
  formalisation counts strong-link references only, which yields a
  predicate that lower-bounds the paper's; every block forming the
  formalisation's pattern forms the paper's pattern.

---

## BibTeX

```bibtex
@inproceedings{Moura021,
  author       = {Leonardo de Moura and
                  Sebastian Ullrich},
  editor       = {Andr{\'{e}} Platzer and
                  Geoff Sutcliffe},
  title        = {{The Lean 4 Theorem Prover and Programming Language}},
  booktitle    = {CADE},
  series       = {LNCS},
  pages        = {625--635},
  publisher    = {Springer},
  year         = {2021},
  url          = {https://doi.org/10.1007/978-3-030-79876-5\_37},
  doi          = {10.1007/978-3-030-79876-5\_37},
}
```

```bibtex
@article{aristotle,
  author       = {Tudor Achim and
                  Alex Best and
                  Alberto Bietti and
                  Kevin Der and
                  Math{\"{\i}}s F{\'{e}}d{\'{e}}rico and
                  Sergei Gukov and
                  Daniel Halpern{-}Leistner and
                  Kirsten Henningsgard and
                  Yury Kudryashov and
                  Alexander Meiburg and
                  Martin Michelsen and
                  Riley Patterson and
                  Eric Rodriguez and
                  Laura Scharff and
                  Vikram Shanker and
                  Vladmir Sicca and
                  Hari Sowrirajan and
                  Aidan Swope and
                  Matyas Tamas and
                  Vlad Tenev and
                  Jonathan Thomm and
                  Harold Williams and
                  Lawrence Wu},
  title        = {Aristotle: IMO-level Automated Theorem Proving},
  journal      = {CoRR},
  volume       = {abs/2510.01346},
  year         = {2025},
  url          = {https://doi.org/10.48550/arXiv.2510.01346},
  doi          = {10.48550/ARXIV.2510.01346},
}
```