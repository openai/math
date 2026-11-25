import OAI.Hierarchy.DescentPackingOrdinals
import Mathlib.Data.Nat.Pairing

namespace OAI
/-! # Exact comparisons of full interval codes using a shared coarse block -/
namespace Hierarchy.DescentResetDyadicOrder

/-- The physical address of the old dyadic interval reconstructed from its
coarse prefix and bounded suffix. -/
def address (coarse depth low : Nat) := coarse*2^depth+low

def raw (base coarse depth low : Nat) := Nat.pair (base+depth) (address coarse depth low)

/-- For nonzero prefixes, every suffix on an earlier depth lies before every
suffix on the next depth. For the exceptional zero prefix the comparison uses
the two true local suffixes and the public depth offset. -/
def before (base : Nat) (zero : Bool) (d x t y : Nat) : Prop :=
  if zero then Nat.pair (base+d) x < Nat.pair (base+t) y else d<t ∨ d=t ∧ x<y

theorem address_before (coarse d x t y : Nat) (positive : 0<coarse) (short : x<2^d) (earlier : d<t) :
    address coarse d x<address coarse t y := by
  have grow : (coarse+1)*2^d≤coarse*2^t := calc
    (coarse+1)*2^d ≤ (coarse*2)*2^d := Nat.mul_le_mul_right _ (by omega)
    _ = coarse*2^(d+1) := by rw [pow_succ];ring
    _ ≤ coarse*2^t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) earlier)
  unfold address
  rw [Nat.succ_mul] at grow
  omega

theorem raw_before (base coarse d x t y : Nat) (shortX : x<2^d) (shortY : y<2^t) :
    raw base coarse d x<raw base coarse t y ↔ before base (decide (coarse=0)) d x t y := by
  by_cases zero : coarse=0
  · simp [raw,address,before,zero]
  have pos : 0<coarse:=Nat.pos_of_ne_zero zero
  have bit : decide (coarse=0)=false:=by simp [zero]
  simp only [before,bit,Bool.false_eq_true,ite_false]
  have separated {d t x y : Nat} (short : x<2^d) (away : d<t) : raw base coarse d x<raw base coarse t y :=
    (Nat.pair_lt_pair_left (address coarse d x) (Nat.add_lt_add_left away base)).trans
      (Nat.pair_lt_pair_right (base+t) (address_before coarse d x t y pos short away))
  rcases lt_trichotomy d t with low|eqn|high
  · exact iff_of_true (separated shortX low) (Or.inl low)
  · subst t
    simp only [lt_self_iff_false,false_or,true_and]
    unfold raw
    rcases lt_trichotomy x y with lt|same|gt
    · exact iff_of_true (Nat.pair_lt_pair_right _ (Nat.add_lt_add_left lt _)) lt
    · subst y;simp
    · exact iff_of_false (Nat.pair_lt_pair_right _ (Nat.add_lt_add_left gt _)).not_gt gt.not_gt
  · exact iff_of_false (separated shortY high).not_gt (by omega)

theorem raw_reconstruct (base depth idx : Nat) (low : base≤depth) :
    raw base (idx/2^(depth-base)) (depth-base) (idx%2^(depth-base))=Nat.pair depth idx := by
  unfold raw address
  rw [Nat.add_sub_of_le low,Nat.div_add_mod']

end Hierarchy.DescentResetDyadicOrder

end OAI
