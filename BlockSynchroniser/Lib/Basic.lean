/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

# Generic lemmas — `BlockSynchroniser.Lib`

This namespace is for **non-domain-specific** facts (list manipulation,
arithmetic, set theory, etc.) that proofs in this formalization need but
Mathlib doesn't directly provide in the right shape.

Generic helper lemmas land here rather than next to the domain-specific
theorem that uses them. This keeps the BFT-protocol modules focused on
protocol facts.
-/

namespace BlockSynchroniser
namespace Lib

/-- If `List.findSome? f l = some b`, then there exists an element `a` of
`l` for which `f a = some b`. Used by `step_refines_HonestStep` to extract
the active validator from `step`'s `findSome?` call. -/
theorem findSome_witness {α β : Type} (l : List α) (f : α → Option β) (b : β)
    (h : l.findSome? f = some b) : ∃ a, a ∈ l ∧ f a = some b := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons head tail ih =>
    rw [List.findSome?] at h
    match hH : f head with
    | none =>
      rw [hH] at h
      obtain ⟨a, ha_mem, ha_eq⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha_mem, ha_eq⟩
    | some b' =>
      rw [hH] at h
      have hb : b' = b := Option.some.inj h
      exact ⟨head, List.mem_cons_self, hH.trans (by rw [hb])⟩

end Lib
end BlockSynchroniser
