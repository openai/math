import OAI.ThreeFlat.Diagonal.MotifHistoryStep
import OAI.ThreeFlat.Diagonal.ShrinkOwnerKernel
import OAI.ThreeFlat.Diagonal.ShrinkSubdivision

namespace OAI
/-! # Concrete shrinking substitution on a packed lane graph

Each chosen motif term first creates only the four surviving cables. The
second one-term substitution splits them into the balanced numbered ports
of the next degree-regular graph. Both operations retain the same old
site ownership and endpoint convention used by the finite descriptor scan.
-/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction MotifKernel
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L K : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [CommSemiring K]
variable (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
variable (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q)
  (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1 = P.bundle m)

private def demandArgument (m : P.Motif) (j : Fin 6) (a : ∀ i, (oldShape P w).Half i) :
    demandGraph.State (fun e => Fin (2^demandWidth P w num m e)) j := fun k =>
  demandEnd P code w hQ num m (oldEnds P w a false) (oldEnds P w a true) k.1.2 k.1.1

/-- A genuine step on packed input slots using the coefficient maps on the
six-party motif. Its target is the exact crossing graph of `subdivision`. -/
def shrinkingStep (T : P.Motif → Type) [∀ m, Fintype (T m)]
    (I : ∀ m, T m → Fin 8 → Type) [∀ m t e, Fintype (I m t e)] [∀ m t e, Inhabited (I m t e)]
    (eval : ∀ m t j, demandGraph.State (fun e => Fin (2^demandWidth P w num m e)) j →
      supplyGraph.State (I m t) j → K)
    (equation : ∀ m x, demandGraph.wiring (fun e => Fin (2^demandWidth P w num m e)) x =
      ∑ t, supplyGraph.contraction (fun j => eval m t j (x j)))
    (layout : (∀ m, T m) → Bool) {count : ℕ} (enum : Fin count ≃ (∀ m, T m)) :
    Rewrite (oldShape P w) K := by
  letI : ∀ j, Inhabited ((oldShape P w).Half j) := fun _ => ⟨fun e => (⟨0,Nat.two_pow_pos _⟩ : Fin (2^w e.val.1))⟩
  apply historyStep (oldShape P w) T (fun _ => supplyGraph) I (fun h => partySite P (layout h))
    (fun h => P.placement (layout h)) (fun m t j a => eval m t j (demandArgument P w code hQ num m j a)) enum
  · intro h m j a b hab
    apply congrArg (eval m (h m) j)
    unfold demandArgument
    rw [← localPartyState_full P w code hQ num bundled (layout h) m j a,
      ← localPartyState_full P w code hQ num bundled (layout h) m j b]
    apply congrArg (localPartyState P w code hQ num (layout h) m j)
    exact funext fun i => hab i.val i.property
  · intro a
    rw [local_demands_wiring P w code hQ num bundled false]
    simp_rw [localPartyState_full P w code hQ num bundled false]
    apply Finset.prod_congr rfl
    intro m _
    exact equation m (fun j => demandArgument P w code hQ num m j a)

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
