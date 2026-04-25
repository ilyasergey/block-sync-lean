/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

# Generic lemmas — `BlockSynchroniser.Lib`

This namespace is for **non-domain-specific** facts (list manipulation,
arithmetic, set theory, etc.) that proofs in this formalization need but
Mathlib doesn't directly provide in the right shape.

When Aristotle (or a hand proof) introduces a generic helper lemma, it
should land here rather than next to the domain-specific theorem that
uses it. This keeps the BFT-protocol modules focused on protocol facts.

Currently empty — facts are added as proof attempts surface them.
-/

namespace BlockSynchroniser
namespace Lib

-- (Reserved for generic lemmas. Add here as needed.)

end Lib
end BlockSynchroniser
