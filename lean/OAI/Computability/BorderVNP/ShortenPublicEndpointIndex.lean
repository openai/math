import OAI.Computability.BorderVNP.ShortenStaticRowEmit
import OAI.Computability.BorderVNP.ShortenStaticRowHoles

/-! # Fixed pin order for the three old-band rectangles and the paid seed bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing SeedIntervals StaticRows

/-- All band codes occur in the rectangle, including the tail at code zero. -/
noncomputable def bandEquiv (D : ℕ) : Band D ≃ Fin (2*D+1) :=
  Equiv.ofBijective (bandRow D) <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨(bandRow D).injective, by simp [Band,Nat.mul_comm,Nat.add_comm]⟩

private def oldRect (n D : ℕ) : Serializer.Row n D ≃ (Fin 3 × (Fin n × Band D)) where
  toFun r := (r.2.2,r.1,r.2.1)
  invFun r := (r.2.1,r.2.2,r.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] {nSeeds : ℕ}

/-- The cable pin permutation is fixed by the rectangle capacities and the seed numbering.
It is independent of the old occupancy, the current geometry, and the histogram branch. -/
noncomputable def candidateEquiv (n : ℕ) (seed : A ≃ Fin nSeeds) :
    Serializer.Row n D ⊕ (A × TemplateEdge e) ≃ Fin (edgeCapacity e n nSeeds) :=
  let old := (oldRect n D).trans (((Equiv.refl (Fin 3)).prodCongr
    (((Equiv.refl (Fin n)).prodCongr (bandEquiv D)).trans finProdFinEquiv)).trans finProdFinEquiv)
  let bank := (seed.prodCongr (Fintype.equivFin (TemplateEdge e))).trans finProdFinEquiv
  ((old.sumCongr bank).trans finSumFinEquiv).trans (finCongr (by unfold edgeCapacity; ring))

omit [Fintype A] in
/-- Every old-band input pin is the corresponding static candidate, including its holes. -/
theorem candidateEquiv_old (n : ℕ) (seed : A ≃ Fin nSeeds) (r : Serializer.Row n D) :
    candidateEquiv e n seed (.inl r) = bandCandidate e nSeeds r.2.2 r.1 r.2.1 := by
  apply Fin.ext
  rw [bandCandidate_val]
  change (bandRow D r.2.1).val + (2*D+1)*r.1.val + (n*(2*D+1))*r.2.2.val = _
  ring

variable [NeZero D] {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

/-- Every paid-bank input pin occupies the corresponding physical cable row. -/
theorem candidateEquiv_bank {n : ℕ} (old : p.layout.Edge ↪ Fin n) (seed : A ≃ Fin nSeeds)
    (a : A) (u : TemplateEdge e) :
    candidateEquiv e n seed (.inr (a,u)) = edgeRows e p bin perm old seed.toEmbedding (.inr (.inr ⟨a,u⟩)) := by
  apply Fin.ext
  rw [bankRow]
  change 3*(n*(2*D+1)) + ((Fintype.equivFin (TemplateEdge e) u).val + Fintype.card (TemplateEdge e)*(seed a).val) = _
  simp only [Equiv.toEmbedding_apply]
  ring

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
