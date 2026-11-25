import OAI.LinearAlgebra.SpectralBooks.Crossing

/-! # Parallel products of wire networks

Concatenating the wire lists lets each local table evaluate all factors on their
respective blocks. The shared strings of different factors vary independently.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

namespace Crossing

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]

/-- A parallel product of networks, pulled back along a block map at each site,
is a single network whose wire cost is the sum of the costs of the factors. -/
theorem exists_parallelNetwork {B C : I → Type*} {t : ℕ} (c : Fin t → ℕ)
    (W : (r : Fin t) → Fin (c r) → Wire I)
    (T : (r : Fin t) → LocalTables (B := B) (W r) F)
    (block : ∀ i, C i → Fin t → B i) :
    ∃ (n : ℕ) (V : Fin n → Wire I) (U : LocalTables (B := C) V F),
      (∀ x, network V U x = ∏ r, network (W r) (T r) (fun i => block i (x i) r)) ∧
      ∀ length : I → I → ℝ, (∑ k, wireCost length (V k)) =
        ∑ r, ∑ k, wireCost length (W r k) := by
  classical
  let J := (r : Fin t) × Fin (c r)
  let e := (Fintype.equivFin J).symm
  let w : J → Wire I := fun p => W p.1 p.2
  let U : LocalTables (B := C) (w ∘ e) F := fun i x a =>
    ∏ r, T r i (block i x r)
      (fun k => Equiv.piCongrLeft (fun p => (w p).Leg i) e a ⟨r, k⟩)
  refine ⟨_, w ∘ e, U, ?_, ?_⟩
  · intro x
    let S := fun (p : J) => Fin (w p).width → Bool
    let assignments := (Equiv.piCongrLeft S e).trans (Equiv.piCurry fun r k => S ⟨r, k⟩)
    unfold network
    rw [Fintype.prod_sum]
    symm
    apply Fintype.sum_equiv assignments.symm
    intro s
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [U]
    apply Finset.prod_congr rfl
    intro r _
    congr 1
    funext k
    change (w ⟨r, k⟩).basisTerm (s r k) i =
      (Equiv.piCongrLeft (fun p => (w p).Leg i) e
        (fun a => (w (e a)).basisTerm (s (e a).1 (e a).2) i)) ⟨r, k⟩
    let legs := fun (p : J) => (w p).basisTerm (s p.1 p.2) i
    exact (congrFun ((Equiv.piCongrLeft (fun p => (w p).Leg i) e).apply_symm_apply legs)
      ⟨r, k⟩).symm
  · intro length
    exact (e.sum_comp (fun p => wireCost length (w p))).trans (Fintype.sum_sigma _)

end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
