import OAI.Hierarchy.DescentSixPartyProfiles

namespace OAI
/-! # Powering a six-party wire replacement with a fixed summand set

An outer summand records the rounded number of bundles on each permitted edge.
Within a fixed profile the connected supply graph carries a diagonal encoding
the selector sequence, so the set of outer summands is independent of the power.
-/

namespace Hierarchy.DescentSixParty

open Computability.VPVNP Computability.VPVNP.WireTensor Computability.VPVNP.WireTensor.RestrictionClass
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {H : Type} [Fintype H]
variable (src dst : Fin 8 → Fin 6)
variable (conn : ∀ {I : Type}, ∀ x : Fin 6 → I, (∀ e, x (src e) = x (dst e)) → ∀ i j, x i = x j)
variable {C k z : ℕ} (w : H → Fin 8 → ℕ) (cost : ∀ h, ∑ e, w h e ≤ C)

include conn in
/-- One profile needs at most the selector bits and the rounded payload widths.
The identity wire on all supply edges carries one common selector. -/
private theorem profile_restriction (hk : Fintype.card H ≤ 2^k) (hz : 0 < z) (p : Profile C) :
    (∑ a : {a : Fin z → H // profile w cost a hz = p},
      binaryNetworkClass (k := F) src dst (payload w a.1)) ≤
      binaryNetworkClass src dst (fun e => z * ((p.1 e).val + k)) := by
  classical
  let A := {a : Fin z → H // profile w cost a hz = p}
  let W := binaryNetworkClass (k := F) src dst (fun e => z*(p.1 e).val)
  let N := binaryNetworkClass (k := F) src dst (fun _ => z*k)
  have widen (a : A) : binaryNetworkClass (k := F) src dst (payload w a.1) ≤ W := by
    apply wire_width_mono
    intro e
    exact (profile_room w cost a.1 hz e).trans_eq
      (congrArg (fun q : Profile C => z * (q.1 e).val) a.2)
  have count : Fintype.card A ≤ 2^(z*k) := by
    calc
      _ ≤ Fintype.card (Fin z → H) :=
        Fintype.card_le_of_injective (fun x : A => x.val) Subtype.val_injective
      _ = Fintype.card H ^ z := by simp
      _ ≤ (2^k)^z := Nat.pow_le_pow_left hk z
      _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm]
  have diag : ((2^(z*k) : ℕ) : RestrictionClass F (Fin 6)) ≤ N := by
    exact connectedNetwork_restricts_diagonal (k := F) (I := Fin (2^(z*k))) src dst
      (fun x h i j => conn x h i j)
  have code : (Fintype.card A : RestrictionClass F (Fin 6)) ≤ N :=
    (nat_mono_class count).trans diag
  calc
    _ ≤ ∑ _ : A, W := sum_mono_class widen
    _ = W * (Fintype.card A : RestrictionClass F (Fin 6)) := by simp [nsmul_eq_mul, mul_comm]
    _ ≤ W * N := orderBounds.mul_mono W code
    _ = _ := by
      dsimp [W,N]
      rw [← binaryNetworkClass_add]
      simp_rw [Nat.mul_add]

include conn cost in
/-- In every power the same finite set of profiles indexes genuine local tensor
maps. A supply edge of profile width `r` carries `r+k` bundles of `z` bits. -/
theorem powered_ordinary_sum (a b : Fin 2 → Fin 6) (B : ℕ)
    (hk : Fintype.card H ≤ 2^k)
    (seed : binaryNetworkClass (k := F) a b (fun _ => B) ≤
      ∑ h, binaryNetworkClass src dst (w h)) (hz : 0 < z) :
    let X := MotifBase.binaryWires (k := F) a b (fun _ => z*B)
    let Y := fun p : Profile C => MotifBase.binaryWires (k := F) src dst
      (fun e => z * ((p.1 e).val + k))
    ∃ L : ∀ p j, X.Basis j → (Y p).Basis j → F,
      X.coeff = ∑ p, applyLocal (L p) (Y p).coeff := by
  classical
  dsimp only
  apply ordinary_sum_of_class_le
  change binaryNetworkClass (k := F) a b (fun _ => z*B) ≤ _
  calc
    _ = binaryNetworkClass a b (fun _ => B)^z := binaryNetworkClass_pow ..
    _ ≤ (∑ h, binaryNetworkClass src dst (w h))^z := pow_mono_class seed z
    _ = ∑ s : Fin z → H, binaryNetworkClass src dst (payload w s) := by
      rw [Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro s _
      exact (binaryNetworkClass_sum src dst Finset.univ (fun i => w (s i))).symm
    _ = ∑ p : Profile C, ∑ s : {s : Fin z → H // profile w cost s hz = p},
        binaryNetworkClass src dst (payload w s.1) := by
      symm
      exact Fintype.sum_fiberwise (fun s => profile w cost s hz)
        (fun s => binaryNetworkClass src dst (payload w s))
    _ ≤ _ := sum_mono_class (profile_restriction src dst conn w cost hk hz)

end
end Hierarchy.DescentSixParty

end OAI
