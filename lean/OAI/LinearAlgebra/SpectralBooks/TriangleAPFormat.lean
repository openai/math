import OAI.LinearAlgebra.SpectralBooks.Crossing

/-! # The three wires and the progression support

The three edges carry the labels `i`, `j`, and `k`. At each site the two
incident labels form a local basis index. On arithmetic-progression support
those indices determine the entire term.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- A pure basis term of the wire triangle, ordered cyclically at the three sites. -/
def triangleWireTerm (q : ℕ) (s : Fin q × Fin q × Fin q) : Fin 3 → Fin q × Fin q :=
  ![(s.1, s.2.1), (s.2.1, s.2.2), (s.2.2, s.1)]

theorem triangleWireTerm_injective (q : ℕ) : Function.Injective (triangleWireTerm q) := by
  intro a b h
  have h₀ : (a.1, a.2.1) = (b.1, b.2.1) := congrFun h 0
  have h₁ : a.2 = b.2 := congrFun h 1
  exact Prod.ext (congrArg (Prod.fst : Fin q × Fin q → Fin q) h₀) h₁

/-- The tensor retaining exactly the triples whose integer labels satisfy `i + k = 2j`. -/
noncomputable def triangleAPTensor (K : Type*) [Field K] (q : ℕ)
    (x : Fin 3 → Fin q × Fin q) : K :=
  ∑ s : Fin q × Fin q × Fin q, if x = triangleWireTerm q s ∧
    (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0 then 1 else 0

end SpectralBooks
end LinearAlgebra
end OAI
