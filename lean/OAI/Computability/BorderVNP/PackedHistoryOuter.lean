import OAI.Computability.BorderVNP.PackedHistoryTensor
import OAI.Computability.BorderVNP.PackedHistoryEpoch

/-! # Repeated public epochs with the exact Proposition 7.2 history index -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing VPVNP.VerifierNetwork

variable {K T : ℕ} {A : ℕ → Type*} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]

/-- A finite prefix of the outer profile expansion in Proposition 7.2. -/
def outerSystem (T : ℕ) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1))) : System K T A :=
  ⟨fun t _ => epoch t⟩

/-- Identical bottom bundles at every leaf. -/
def repeatLeaf {U : Type*} (K : ℕ) (u : U) : (n : ℕ) → Leaves K U n
  | 0 => u
  | n+1 => fun _ => repeatLeaf K u n

private def project {X Y : Type*} (p : ProfileSum X) (f : X → Y) : ProfileSum Y :=
  ⟨p.Index,p.finite,fun q => f (p.term q)⟩

/-- Forgetting only the bookkeeping name gives literally the same dependent profile sum,
including its term map, as the manuscript's recursive packHistory. -/
theorem outer_profiles (bottom : A 0) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1)))
    (d : ℕ) (hd : d ≤ T) :
    let S := outerSystem T epoch
    project (S.histories d hd (repeatLeaf K bottom d)) (S.layer d).state = packHistory bottom epoch d := by
  intro S
  induction d with
  | zero => rfl
  | succ d ih =>
    change combineProfiles (fun _ : Fin K => project (S.histories d (by omega) (repeatLeaf K bottom d))
      (S.layer d).state) (epoch d) = combineProfiles (fun _ => packHistory bottom epoch d) (epoch d)
    rw [ih (by omega)]

/-- Index equivalence for the true outer pack history after all finite shortening epochs. -/
def outerEquiv (bottom : A 0) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1))) (d : ℕ) (hd : d ≤ T) :
    ((outerSystem T epoch).histories d hd (repeatLeaf K bottom d)).Index ≃ (packHistory bottom epoch d).Index :=
  Equiv.cast (congrArg ProfileSum.Index (outer_profiles bottom epoch d hd))

private theorem term_cast {U : Type*} {p q : ProfileSum U} (h : p=q) (i : p.Index) :
    q.term ((Equiv.cast (congrArg ProfileSum.Index h)) i) = p.term i := by subst q; rfl

/-- The index equivalence preserves the actual physical pack, even when many profile choices
lead to the same pack. -/
theorem outerEquiv_state (bottom : A 0) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1)))
    (d : ℕ) (hd : d ≤ T) (q : ((outerSystem T epoch).histories d hd (repeatLeaf K bottom d)).Index) :
    (packHistory bottom epoch d).term (outerEquiv bottom epoch d hd q) = state d hd (repeatLeaf K bottom d) q :=
  term_cast (outer_profiles bottom epoch d hd) q

variable {σ : Type*} [Fintype σ]

/-- Combining the true outer history equivalence with the physical bit verifier gives exactly
one public assignment per Proposition 7.2 summand. The local frame may itself be flatEpoch,
including all subrounds inside each epoch. -/
noncomputable def acceptedOuter (bottom : A 0) (epoch : ∀ t, (Fin K → A t) → ProfileSum (A (t+1)))
    (C : Codec (outerSystem T epoch) G) (rep : Represents A W) (step : Steps K T W G)
    (correct : LocalCorrect C rep step) (f : Frame σ (W 0)) (x : σ → Bool) (h : rep 0 (f.eval x) bottom) :
    (packHistory bottom epoch T).Index ≃
      {g : Slot K G T → Bool // flag step T le_rfl (repeatLeaf K f T) x g = true} := by
  have hl (n : ℕ) : LeafState rep x n (repeatLeaf K bottom n) (repeatLeaf K f n) := by
    induction n with
    | zero => exact h
    | succ n ih => exact fun _ => ih
  exact (outerEquiv bottom epoch T le_rfl).symm.trans
    (acceptedEquiv C rep step correct T le_rfl (repeatLeaf K bottom T) (repeatLeaf K f T) x (hl T))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
