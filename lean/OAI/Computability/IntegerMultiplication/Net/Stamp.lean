import OAI.Computability.IntegerMultiplication.Net.Special
import OAI.Computability.IntegerMultiplication.Net.Rational

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
open Finset Matrix Tensor Motif Halo
variable {J T : Type} [DecidableEq J] [Fintype J] [DecidableEq T]

structure Stamp (J : Type) where
  v : Addr J
  night : Bool

def bill (v : Stamp J) : Addr J → Clock :=
  fun x => (if v.night then -1 else 1)*digit (v.v ⬝ᵥ x)

def slip (dark : Bool) (q : Addr J) : Stamp J :=
  let k := if dark then -weight q else weight q
  ⟨q, decide (k≠1)⟩

omit [DecidableEq J] in
theorem lists (dark : Bool) (q : Addr J) (hq : q ⬝ᵥ q = 1) :
    bill (slip dark q) =
      fun x => (if dark then -weight q else weight q)*digit (q ⬝ᵥ x) := by
  have e := tick (weight q) (odd q hq)
  rcases e with w|w
  all_goals cases dark <;> simp (config := {decide:=true}) [w,slip]
  all_goals funext _; simp [bill]

noncomputable def manifest (z : Chart J B) (t : Finset J) (d : Bool) :=
  t.toList.map (fun i => slip d (z.primal i))

theorem distinctBill (z : Chart J B) (h : z.pull = z.push.transpose)
    (t : Finset J) (d : Bool) :
    ((manifest z t d).map bill).sum =
      (fun x => if d then - weight ((∑ i∈t, z.ray i) *ᵥ x)
        else weight ((∑ i∈t, z.ray i) *ᵥ x)) := by
  rw [manifest,List.map_map, Finset.sum_map_toList]
  funext x
  simp_rw [song z h, Finset.sum_apply, Function.comp_apply]
  have e i := lists d (z.primal i) (by simpa using respects z h i i)
  simp_rw [e]
  cases d <;> simp [Finset.sum_neg_distrib]

theorem num (z : Chart J B) (t : Finset J) (d : Bool) :
    (manifest z t d).length=t.card := by simp [manifest]

variable (P : T → Mat J B)
def standing (l : Place T) (x : Addr (S → J)) := weight (operator P l *ᵥ x)

omit [DecidableEq T] in
theorem advance (u v : Place T) (a :
    decorated P (fun Z => Z.pull=Z.push.transpose) u v) :
    ∃ l : List (Stamp (S→J)),
      (l.map bill).sum = standing P v - standing P u ∧
        (∀ s∈l, s.v ⬝ᵥ s.v = 1) ∧
        (l.length : ℤ) ≤ Place.allowance (Fintype.card J) u v := by
  obtain ⟨e,f,i,W,h,ma,mb,r⟩ := a
  let z := weave W
  have oz : z.pull=z.push.transpose := by simp [z,weave,Tensor.flip,h]
  let U := canvas i u
  let V := canvas i v
  have rule (w : Place T) (h : material i P W w) (x : Addr (S→J)) :
      standing P w x =
      ∑ j∈canvas i w, weight (z.primal j)*digit (z.primal j ⬝ᵥ x) := by
    rw [standing, h,shade_rays]
    exact song z oz _ _
  have ready (t : Finset (S→J)) (d : Bool) : ∀ s∈manifest z t d, s.v ⬝ᵥ s.v=1 := by
    intro s ss; rcases List.mem_map.mp ss with ⟨a,_,rfl⟩
    simp only [slip, respects z oz,ite_true] --?
  have sizes : |(V.card:ℤ)-(U.card:ℤ)| ≤ Place.allowance (Fintype.card J) u v := by
    rw [Halo.eval i u e, Halo.eval i v f, Place.allowance]
    split <;> omega
  rcases r with r|r
  · refine ⟨manifest z (V\U) false, ?_, ready _ _, ?_⟩
    · funext x
      change U ⊆ V at r
      rw [distinctBill z oz]
      simp only [Pi.sub_apply,rule _ ma,rule _ mb,song z oz,Bool.false_eq_true,ite_false]
      exact eq_sub_of_add_eq (Finset.sum_sdiff r)
    apply le_trans _ sizes
    rw [num,card_sdiff_of_subset r,Nat.cast_sub (card_le_card r)]
    exact le_abs_self _
  refine ⟨manifest z (U\V) true, ?_, ready _ _, ?_⟩
  · rw [distinctBill z oz]
    funext x
    simp only [Pi.sub_apply,rule _ ma,rule _ mb,song z oz,ite_true]
    change -_ = (∑ j∈V, weight (z.primal j)*digit (z.primal j ⬝ᵥ x)) -
      (∑ j∈U, weight (z.primal j)*digit (z.primal j ⬝ᵥ x))
    rw [← neg_sub (∑ j∈U, weight (z.primal j)*digit (z.primal j ⬝ᵥ x))
      (∑ j∈V, weight (z.primal j)*digit (z.primal j ⬝ᵥ x))]
    congr 1
    exact eq_sub_of_add_eq (Finset.sum_sdiff r)
  apply le_trans _ sizes
  rw [num,card_sdiff_of_subset r,Nat.cast_sub (card_le_card r),abs_sub_comm]
  exact le_abs_self _
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
