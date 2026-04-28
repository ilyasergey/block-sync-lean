# Suggested edits to the Beluga manuscript — Stage 4

A short follow-up to [`paper-additions-stage3.md`](paper-additions-stage3.md),
prompted by the Mysticeti-Beluga consensus-liveness layer (paper
Appendix D.2). Stage 3 covered the §5 partial-synchrony assumption
(six items). Stage 4 extends it with two paper-implicit items
needed by §D.2.

---

## 1. Extend the §5 partial-synchrony assumption with two §4.2
per-action items

Stage-3 §2 proposed the *Beluga partial-synchrony assumption*
with six items (clock; push delivery; `T_rd = 5Δ` round timeout;
protocol synchronization; accept-action liveness; in-pool
delivery). The §D.2 proofs surface two more paper-implicit items.

The §4.2 prose treats all four protocol actions — `propose`,
`accept`, `store`, `advance` — symmetrically as per-action
liveness primitives ("honest validators run the protocol"). The
six-item §5 assumption already names three of the four (delivery
is the §2 channel; accept is item 5; advance is items 3 + 4
through `T_rd` and protocol synchronization). The §D.2 proofs
additionally consume:

> **Item 5b (Propose-action liveness — §4.2).** *Post-GST, when
> an honest validator at round `r` has not yet proposed for `r`,
> it does so within `Δ`.*

Used in the §D.2 Lemma 7 proof: *"Then the honest leader
validator will directly create and disseminate the round `r`
leader block `B_L^r`, which will take another `Δ` to be received
by every honest validator."* The "directly create" step is exactly
this propose-action `Δ`-bound.

> **Item 5c (Store-action liveness — §4.2).** *Post-GST, when an
> honest validator has accepted a block but not yet stored it, it
> stores within `Δ`.*

Used implicitly in §D.2 Theorem 6's *"the leader block and its
causal history blocks will eventually be output via
`block_store`"* — the `Δ`-bound on the store action is what makes
"eventually" hold within bounded time.

Both items are direct mirrors of item 5 (accept-action liveness)
applied to the other two output actions, and faithfully follow
the §4.2 symmetric prose.

---

## 2. §D.2 self-contained, no further amendments needed

§D.2's Lemmas 7–12 and Theorem 6 are self-contained derivations
from §5 + §4.2/4.3 + §D.1 protocol mechanics. No paper change is
needed for §D.2 to be sound; the round-02 manuscript is already
correct. The only paper-side action item from §D.2 is the
extension of the §5 assumption above (items 5b, 5c).

The Mysticeti consensus rules (`directDecide`, `indirectDecide`,
the round-robin leader schedule) are already paper-stated; the
safety lemmas (L13–L16, T7) are already covered by the
"inherent facts" enumeration in §D.3 (introduced in round-02 to
close round-01 finding F-5).

---

## 3. Summary table (cumulative across stages 3 + 4)

| Section | Edit | Stage |
|---|---|---|
| §5 (Lemma 1) | Pin the quantifier order | 3 |
| §4.2 (rule iii) | Pin the target round and trigger | 3 |
| §5 (before Lemma 1) | State the partial-synchrony assumption (six items) | 3 |
| §4.3 | Name the pull-mechanism conclusion + ImPoA's two roles | 3 |
| §C.2 (Lemmas 3, 4, 5) | Cite Assumption 1 in proof bodies | 3 |
| §5 (former round-latency lemma) | Note consolidation into Theorem 3, or restore | 3 |
| §4 / Figure 8 | Make accept/store atomicity explicit, or split with action priority | 3 |
| §5 (assumption — extension) | **Add items 5b and 5c (propose/store-action liveness)** | **4** |
