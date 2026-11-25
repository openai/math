import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementAssembly

/-! # Removing the padded exterior indices after tree replacement

An exterior assignment outside the original alphabet has an illegal label at
the tail stub of some wire. The open value of its patch is zero, so the entire
product vanishes. On the remaining assignments restriction of the alphabet is
a bijection, including when there are no exterior wires.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped Classical BigOperators

namespace PortGraph.StubPairing

universe u
variable {J : Type u} {S : J → Type u} [Fintype J]
variable (C : StubPairing S) {R : Type*} [CommSemiring R] {q D : ℕ}

/-- Restrict the exterior state sum to the embedded original alphabet. -/
theorem sum_boundary_castLE (hq : q ≤ D) (U : (j : J) → (S j → Fin D) → R)
    (hzero : ∀ j y s, q ≤ (y s).val → U j y = 0) :
    (∑ x : C.Wire → Fin D, ∏ j, U j (fun s => x (C.ends.symm ⟨j,s⟩).1)) =
      ∑ x : C.Wire → Fin q, ∏ j, U j (fun s => (x (C.ends.symm ⟨j,s⟩).1).castLE hq) := by
  symm
  let emb (x : C.Wire → Fin q) (e : C.Wire) := (x e).castLE hq
  apply Fintype.sum_of_injective emb
  · intro x y h
    funext e
    exact Fin.castLE_injective hq (congrFun h e)
  · intro y hy
    have hex : ∃ e, q ≤ (y e).val := by
      by_contra! h
      exact hy ⟨fun e => ⟨(y e).val,h e⟩,rfl⟩
    obtain ⟨e,he⟩ := hex
    let p := C.ends (e,false)
    apply Finset.prod_eq_zero (Finset.mem_univ p.1)
    apply hzero p.1 _ p.2
    simpa [p] using he
  · intro x
    rfl

/-- Replace the open evaluations by their original-alphabet values when they
agree on embedded tuples and vanish on every out-of-range tuple. -/
theorem sum_boundary_eq_original (hq : q ≤ D) (U : (j : J) → (S j → Fin D) → R)
    (V : (j : J) → (S j → Fin q) → R)
    (hzero : ∀ j y s, q ≤ (y s).val → U j y = 0)
    (hlegal : ∀ j x, U j (fun s => (x s).castLE hq) = V j x) :
    (∑ x : C.Wire → Fin D, ∏ j, U j (fun s => x (C.ends.symm ⟨j,s⟩).1)) =
      ∑ x : C.Wire → Fin q, ∏ j, V j (fun s => x (C.ends.symm ⟨j,s⟩).1) := by
  rw [C.sum_boundary_castLE hq U hzero]
  exact Finset.sum_congr rfl (fun x _ => Finset.prod_congr rfl (fun j _ =>
    hlegal j (fun s => x (C.ends.symm ⟨j,s⟩).1)))

end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
