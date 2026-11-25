import OAI.ThreeFlat.Diagonal.ShrinkActiveSites
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCopyBudget

namespace OAI
/-! # Charging the copies in the actual occupied shrink-site records -/

namespace ThreeFlat.Diagonal

open Computability.VPVNP.Compression CompressorPacking MotifKernel
open scoped Classical BigOperators
noncomputable section

/-- A motif appears at most once at each site it touches. Choosing one of
its parties at that site embeds the occupied pairs into all motif-party pairs. -/
theorem MotifKernel.sum_active_cost_le {M G J : Type} [Fintype M] [Fintype G] [Fintype J]
    (place : M → J → G) (r : M → ℕ) :
    (∑ v, ∑ a : Active place v, r a.val) ≤ Fintype.card J*∑ m, r m := by
  let send (z : Σ v, Active place v) : M × J := (z.2.val,z.2.property.choose)
  have hinj : Function.Injective send := by
    rintro ⟨v,⟨m,a⟩⟩ ⟨w,⟨n,b⟩⟩ h
    have hm : m = n := congrArg Prod.fst h
    subst n
    have hj : a.choose = b.choose := congrArg Prod.snd h
    have hv : v=w := a.choose_spec.symm.trans ((congrArg (place m) hj).trans b.choose_spec)
    subst w
    rfl
  calc
    _ = ∑ z : Σ v, Active place v, r z.2.val := (Fintype.sum_sigma _).symm
    _ ≤ ∑ p : M × J, r p.1 := Finset.sum_le_sum_of_injOn send hinj.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]

namespace CompressorPacking.Local

variable {c d : ℕ} {V H Tag L : Type} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (layout : Bool)

/-- Copies of the occupied motifs at this particular output site. -/
def activeCopiesAt (r : P.Motif → ℕ) (v : Site V Tag L) : ℕ :=
  ∑ a : MotifKernel.Active (partySite P layout) v, r a.val

/-- The native compact table removes duplicate parties. Its active motif sum
therefore obeys both the global six-party charge and the fixed slot capacity. -/
theorem active_copies_bound (r : P.Motif → ℕ) {R : ℕ} (hr : ∀ m, r m ≤ R) :
    (∑ v, activeCopiesAt P layout r v) ≤ 6*∑ m, r m ∧
    ∀ v, activeCopiesAt P layout r v ≤ (8*d^2*2^c)*R := by
  unfold activeCopiesAt
  constructor
  · have total := MotifKernel.sum_active_cost_le (partySite P layout) r
    simp only [Fintype.card_fin] at total
    refine (Nat.le_of_eq ?_).trans total
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr _ (fun _ _ => rfl)
    exact congrArg (fun t : Fintype (MotifKernel.Active (partySite P layout) v) => @Finset.univ _ t)
      (Subsingleton.elim _ _)
  · intro v
    let ord := (Fintype.equivFin (Slots d c)).symm
    have card : Fintype.card (MotifKernel.Active (partySite P layout) v) ≤ 8*d^2*2^c := calc
      _ = _ := Fintype.card_congr (activeEquiv P layout v ord).symm
      _ ≤ Fintype.card (Fin (Fintype.card (Slots d c))) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by rw [Fintype.card_fin,slot_count]
    calc
      _ ≤ ∑ _ : MotifKernel.Active (partySite P layout) v, R :=
        Finset.sum_le_sum fun a _ => hr a.val
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _ ≤ _ := Nat.mul_le_mul_right R card

/-- Both bounds on the six-party list, with its global and per-motif budgets. -/
def ActiveCopyBounds (r : P.Motif → ℕ) (total peak : ℕ) : Prop :=
  (∑ v, activeCopiesAt P layout r v) ≤ 6*total ∧
  ∀ v, activeCopiesAt P layout r v ≤ (8*d^2*2^c)*peak

theorem active_copies_of_budget (r : P.Motif → ℕ) (total peak : ℕ)
    (budget : (∑ m,r m)≤total ∧ ∀ m,r m≤peak) : ActiveCopyBounds P layout r total peak := by
  have a := active_copies_bound P layout r budget.2
  exact ⟨a.1.trans (Nat.mul_le_mul_left 6 budget.1),a.2⟩

end CompressorPacking.Local

namespace PhysicalStage

attribute [local irreducible] Ordered.binaryPacking shrinkCopies

set_option maxHeartbeats 800000 in
/-- The actual native rows of the binary packing, counted over the selected layout. -/
theorem shrinkCopies_active_bounds {F : Type} [Field F] (T : ShrinkMotif.Table F) (s rem : ℕ)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) (layout : Bool) :
    let d := 2^s
    let c := 2*d+1
    Local.ActiveCopyBounds (d:=d) (c:=c) (V:=A.Base) (H:=BitWord s)
      (Tag:=BitWord (CompressorPacking.tagBits d)) (L:=BitWord rem)
      (Ordered.binaryPacking A.order.symm A.graph) layout (shrinkCopies T s rem A)
      (d*A.positions+A.widthSum) (shrinkCopyFactor c d*(1+A.maxWidth)) := by
  exact Local.active_copies_of_budget (d:=2^s) (c:=2*(2^s)+1) (V:=A.Base) (H:=BitWord s)
    (Tag:=BitWord (CompressorPacking.tagBits (2^s))) (L:=BitWord rem)
    (Ordered.binaryPacking A.order.symm A.graph) layout (shrinkCopies T s rem A) _ _
    (shrinkCopies_bounds T s rem A)

end PhysicalStage
end
end ThreeFlat.Diagonal

end OAI
