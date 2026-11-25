import OAI.Computability.BorderVNP.CoverDeckGreedy
import OAI.Computability.VPVNP.VerifierMachineDecodeMatch

/-!
# Listing the children of a dynamically supplied product-cover residue

One shared literal test identifies each possible parent in the public table.
The second gate layer reads the addresses of that parent's children in
ascending canonical order. The number of tests is the number of actual
parent tiles, independently of the ambient binary key space.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame)
open VPVNP.VerifierMachineDecode
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Number of children of any parent at the given level. -/
noncomputable def childCount (q d : ℕ) :=
  (CoverDeck.fiber (productReduction q (Nat.le_succ d)) 1).card

/-- The first quotient layer may be smaller than later layers. Every layer
used in digit refinement has at most this fixed number of children. -/
theorem childCount_le (q d : ℕ) (hd : 1 ≤ d) : childCount q d ≤ 7^(3*q) := by
  rcases d with _ | _ | d
  · omega
  · have h := Finset.card_le_univ (CoverDeck.fiber (productReduction q (Nat.le_succ 1)) 1)
    simp only [Fintype.card_fun,Fintype.card_fin,← Nat.card_eq_fintype_card (α := Deck _),deck_card] at h
    exact h.trans ((Nat.pow_le_pow_left tileCount_two_bounds.2 q).trans_eq (pow_mul ..).symm)
  · exact (product_children_card q d 1).le

/-- The fiber over the identity contains the identity. -/
theorem childCount_pos (q d : ℕ) : 0 < childCount q d := by
  exact Finset.card_pos.mpr ⟨1,by simp [CoverDeck.fiber]⟩

/-- The ordered child list has the same length at each parent. -/
theorem digitChildren_length (q d : ℕ) (u : Fin q → Deck d) :
    (digitChildren q d u).length = childCount q d := by
  simpa [digitChildren,childCount] using
    CoverDeck.fiber_card_eq_kernel _ (productReduction_surjective q (Nat.le_succ d)) u

/-- The child with a specified position in the ordered list. -/
noncomputable def childAt (q d : ℕ) (u : Fin q → Deck d) (j : Fin (childCount q d)) :
    Fin q → Deck (d+1) := (digitChildren q d u)[j.val]'(by rw [digitChildren_length]; exact j.isLt)

theorem childAt_list (q d : ℕ) (u : Fin q → Deck d) :
    List.ofFn (childAt q d u) = digitChildren q d u := by
  apply List.ext_getElem (by simp [digitChildren_length])
  intros
  simp [childAt]

private def parentTest (q d : ℕ) (u : Fin q → Deck d) :=
  matchAt (keyWidth q d) 0 (List.ofFn (keyWord q d u))

private theorem parentTest_eval (q d : ℕ) (u v : Fin q → Deck d) :
    (parentTest q d v).eval (keyWord q d u) = decide (u = v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [parentTest,eval_matchAt_drop,Nat.zero_le,List.drop_zero,true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht⟩
    have hlen := congrArg List.length ht
    simp only [List.length_append,List.length_ofFn] at hlen
    have hempty : t = [] := List.length_eq_zero_iff.mp (by omega)
    have hw := List.ofFn_injective (by simpa [hempty] using ht)
    apply (productKey q d).injective
    exact congrArg (ParseBatchCounts.numberWords _) hw
  · rintro rfl
    exact ⟨[],by simp⟩

private noncomputable def parentFlags (q d : ℕ) : Frame (Fin (keyWidth q d)) (Fin q → Deck d) :=
  (Frame.initial id).step (parentTest q d)

private theorem parentFlags_size (q d : ℕ) : (parentFlags q d).size ≤
    Fintype.card (Fin q → Deck d) * (3 * keyWidth q d + 1) := by
  apply (Frame.step_size_le (Frame.initial id) (parentTest q d) _ ?_).trans_eq (Nat.zero_add _)
  intro u
  simpa [parentTest] using size_matchAt (keyWidth q d) 0 (List.ofFn (keyWord q d u))

/-- Shared parent equality tests followed by hardwired table reads. -/
noncomputable def childrenFrame (q d : ℕ) :
    Frame (Fin (keyWidth q d)) (Fin (childCount q d) × Fin (keyWidth q (d+1))) :=
  (parentFlags q d).step fun p =>
    StatementCircuit.table (fun u => keyWord q (d+1) (childAt q d u p.1) p.2)
      StatementCircuit.Expr.input true

/-- On canonical product-address wires, every output row is the indicated
child of the supplied parent. -/
theorem childrenFrame_eval (q d : ℕ) (u : Fin q → Deck d) (j : Fin (childCount q d))
    (b : Fin (keyWidth q (d+1))) :
    (childrenFrame q d).eval (keyWord q d u) (j,b) = keyWord q (d+1) (childAt q d u j) b := by
  rw [childrenFrame,Frame.step_eval]
  have hf (v : Fin q → Deck d) :
      (StatementCircuit.Expr.input v).eval ((parentFlags q d).eval (keyWord q d u)) = decide (u=v) := by
    have hid : (Frame.initial id).eval (keyWord q d u) = keyWord q d u :=
      funext (Frame.initial_eval id (keyWord q d u))
    simpa [parentFlags,StatementCircuit.Expr.eval,hid] using parentTest_eval q d u v
  simpa using StatementCircuit.eval_table ((parentFlags q d).eval (keyWord q d u))
    (fun v => keyWord q (d+1) (childAt q d v j) b) StatementCircuit.Expr.input u hf true

/-- The table circuit has linear cost in the actual number of parents at
fixed output arity and key width. -/
theorem childrenFrame_size (q d : ℕ) : (childrenFrame q d).size ≤
    Fintype.card (Fin q → Deck d) * (3 * keyWidth q d + 1) +
    (childCount q d * keyWidth q (d+1)) * (Fintype.card (Fin q → Deck d) * 4 + 1) := by
  unfold childrenFrame
  have h := Frame.step_size_le (parentFlags q d)
    (fun (p : Fin (childCount q d) × Fin (keyWidth q (d+1))) =>
      StatementCircuit.table (fun u => keyWord q (d+1) (childAt q d u p.1) p.2)
        StatementCircuit.Expr.input true) _ (fun _ => StatementCircuit.size_table_le _ _ _ 1 (fun _ => le_rfl))
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact h.trans (Nat.add_le_add_right (parentFlags_size q d) _)

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
