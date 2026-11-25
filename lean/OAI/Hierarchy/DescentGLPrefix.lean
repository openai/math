import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Prefix fibers in the binary layout space -/

namespace Hierarchy.DescentGL

open scoped Classical
abbrev Bits (k : ℕ) := Fin k → ZMod 2
abbrev Nonzero (k : ℕ) := {x : Bits k // x ≠ 0}

def headRows {k j : ℕ} (hj : j≤k) (v : Bits k) : Bits j := fun i => v (i.castLE hj)

theorem card_bits (k : ℕ) : Fintype.card (Bits k)=2^k := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem card_nonzero (k : ℕ) : Fintype.card (Nonzero k) = 2^k-1 := by
  change Fintype.card {x : Bits k // ¬x=0} = _
  rw [Fintype.card_subtype_compl, card_bits, Fintype.card_subtype_eq]

private def tailEquiv (j r : ℕ) :
    {v : Nonzero (j+r) // headRows (Nat.le_add_right j r) v.val=0} ≃ Nonzero r where
  toFun v := ⟨fun i => v.val.val (Fin.natAdd j i), by
    intro hs
    apply v.val.property
    funext i
    refine Fin.addCases (fun l => ?_) (fun u => ?_) i
    · exact congrFun v.property l
    · exact congrFun hs u⟩
  invFun t := ⟨⟨Fin.append (0 : Bits j) t.val, by
      intro hs
      apply t.property
      funext i
      simpa using congrFun hs (Fin.natAdd j i)⟩, by
    funext i
    exact Fin.append_left (0 : Bits j) t.val i⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun l => ?_) (fun u => ?_) i
    · exact (Fin.append_left (0 : Bits j) (fun z => v.val.val (Fin.natAdd j z)) l).trans
        (congrFun v.property l).symm
    · exact Fin.append_right (0 : Bits j) (fun z => v.val.val (Fin.natAdd j z)) u
  right_inv t := by
    apply Subtype.ext
    funext i
    exact Fin.append_right (0 : Bits j) t.val i

theorem zero_prefix_card {k j : ℕ} (hj : j≤k) :
    Fintype.card {v : Nonzero k // headRows hj v.val=0} = 2^(k-j)-1 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa using (Fintype.card_congr (tailEquiv j r)).trans (card_nonzero r)

end Hierarchy.DescentGL

end OAI
