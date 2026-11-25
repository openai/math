import OAI.Computability.VPVNP.MotifBase

namespace OAI
/-! # Bounded bundle profiles for a powered finite wire identity -/

namespace Hierarchy.DescentSixParty

open scoped BigOperators Classical
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.VPVNP.WireTensor.RestrictionClass
noncomputable section

/-- This finite set of rounded width vectors is fixed before the tensor power is chosen. -/
abbrev Profile (C : ℕ) := {p : Fin 8 → Fin (C+2) // (∑ e, (p e).val) ≤ C+8}

theorem profile_card (C : ℕ) : Fintype.card (Profile C) ≤ (C+2)^8 := by
  simpa using Fintype.card_le_of_injective (fun p : Profile C => p.val) Subtype.val_injective

variable {H : Type} [Fintype H] (w : H → Fin 8 → ℕ) {C z : ℕ}
variable (cost : ∀ h, ∑ e, w h e ≤ C)

def payload (a : Fin z → H) (e : Fin 8) : ℕ := ∑ i, w (a i) e

include cost in
omit [Fintype H] in
private theorem total_payload_le (a : Fin z → H) : ∑ e, payload w a e ≤ z*C := by
  unfold payload
  rw [Finset.sum_comm]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => cost (a i))

include cost in
omit [Fintype H] in
private theorem quotients_le (a : Fin z → H) (hz : 0 < z) :
    (∑ e, payload w a e / z) ≤ C := by
  apply Nat.le_of_mul_le_mul_right _ hz
  rw [Finset.sum_mul]
  exact (Finset.sum_le_sum (fun e _ => Nat.div_mul_le_self (payload w a e) z)).trans
    ((total_payload_le w cost a).trans_eq (Nat.mul_comm _ _))

def profile (a : Fin z → H) (hz : 0 < z) : Profile C := by
  let p (e : Fin 8) : Fin (C+2) :=
    ⟨payload w a e / z + 1, by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun i => payload w a i / z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      have h' := quotients_le w cost a hz
      omega⟩
  refine ⟨p, ?_⟩
  change (∑ e, (payload w a e / z + 1)) ≤ C + 8
  simpa [Finset.sum_add_distrib] using Nat.add_le_add_right (quotients_le w cost a hz) 8

omit [Fintype H] in
theorem profile_room (a : Fin z → H) (hz : 0 < z) (e : Fin 8) :
    payload w a e ≤ z * ((profile w cost a hz).1 e).val :=
  (Nat.lt_mul_div_succ (payload w a e) hz).le

theorem profile_cost (s : ℕ) (p : Profile C) :
    (∑ e, ((p.1 e).val + s)) ≤ C + 8 + 8*s := by
  simpa [Finset.sum_add_distrib] using Nat.add_le_add_right p.2 (8*s)

section
variable {F : Type*} [Field F] {J : Type} [Fintype J] [Nonempty J]

private abbrev Class := RestrictionClass F J

theorem sum_mono_class {I : Type*} [Fintype I] {f g : I → Class (F := F) (J := J)}
    (h : ∀ i, f i ≤ g i) : ∑ i, f i ≤ ∑ i, g i := by
  classical
  have bound (A : Finset I) : ∑ i ∈ A, f i ≤ ∑ i ∈ A, g i := by
    induction A using Finset.induction_on with
    | empty => simp
    | insert i A hi ih => simpa [hi] using orderBounds.add_mono (h i) ih
  exact bound Finset.univ

theorem pow_mono_class {a b : Class (F := F) (J := J)} (h : a ≤ b) (z : ℕ) :
    a^z ≤ b^z := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [pow_succ, pow_succ]
    exact (orderBounds.mul_mono (a^z) h).trans (by simpa [mul_comm] using orderBounds.mul_mono b ih)

theorem nat_mono_class {a b : ℕ} (h : a ≤ b) :
    (a : Class (F := F) (J := J)) ≤ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using (orderBounds.add_mono (le_refl (a : Class (F := F) (J := J)))
    (orderBounds.zero_le (d : Class (F := F) (J := J))))

theorem wire_width_mono {E : Type} [Fintype E] (src dst : E → J) {p q : E → ℕ}
    (h : ∀ e, p e ≤ q e) :
    binaryNetworkClass (k := F) src dst p ≤ binaryNetworkClass src dst q := by
  classical
  let d (e : E) := q e - p e
  have hd : (fun e => p e + d e) = q := funext fun e => Nat.add_sub_of_le (h e)
  have one : (1 : Class (F := F) (J := J)) ≤ binaryNetworkClass src dst d := by
    apply orderBounds.one_le
    intro zero
    have hzero := (ofTensor_eq_zero_iff _).1 zero
    let edge (e : E) : Fin (2^d e) := ⟨0, Nat.two_pow_pos _⟩
    have bad := congrFun hzero (edgeAssignment src dst edge)
    change _ = (0 : F) at bad
    simp [wireNetwork, edgeAssignment] at bad
  rw [← hd, binaryNetworkClass_add]
  simpa using orderBounds.mul_mono (binaryNetworkClass (k := F) src dst p) one

end
end
end Hierarchy.DescentSixParty

end OAI
