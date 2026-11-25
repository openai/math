import OAI.Computability.BorderVNP.PackedSewnFragmentPairTest
import OAI.Computability.BorderVNP.PackedSewnFragmentPairSize

/-! # Observable correctness of the two-fragment coalescing circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open PairGate

variable {w : ℕ}

private theorem saved (x : Raw w → Bool) (p : Raw w) : (loaded w).eval x (.inl p) = x p := by
  simp [loaded,loadBit,StatementCircuit.Expr.eval]

private theorem identity_of_false (x : Raw w → Bool) (hm : merge.eval ((loaded w).eval x) = false) :
    (pair w).eval x = x := by
  funext ⟨b,c⟩
  cases b <;> rcases c with f | ⟨k,j⟩
  · cases f <;> simp [pair,outputBit,StatementCircuit.Expr.eval,saved]
  · by_cases h : k = 2 <;> simp [pair,outputBit,h,mux_eval,hm,rawWord,StatementCircuit.Expr.eval,saved]
  · cases f <;> simp [pair,outputBit,flag,hm,StatementCircuit.Expr.eval,saved]
  · simp [pair,outputBit,StatementCircuit.Expr.eval,saved]

private theorem joined_width (x : Raw w → Bool) (hm : merge.eval ((loaded w).eval x) = true)
    (fits : word (fun j => x (false,j)) 2 + word (fun j => x (true,j)) 2 < 2^w) :
    word (fun j => (pair w).eval x (false,j)) 2 =
      word (fun j => x (false,j)) 2 + word (fun j => x (true,j)) 2 := by
  have hs := sum_value x (1 : Fin 3) (by simpa using fits)
  simp only [decide_true] at hs
  simp only [word,pair,Frame.step_eval,outputBit,ite_true,mux_eval,hm]
  exact hs

private theorem identity_absorb {l r : Column w → Bool}
    (h : ¬ (l (.inl false) = true ∧ r (.inl false) = true ∧ (parseRow l).compatible (parseRow r))) :
    absorb (read l) (read r) = (read l,read r) := by
  cases hl : l (.inl false) <;> cases hr : r (.inl false) <;> simp_all [absorb,read]

/-- For every pair of in-bounds enabled descriptors, the circuit returns the exact
joined interval in its left slot and clears its right slot precisely when the two
partial translations continue. -/
theorem pair_spec (w : ℕ) : PairSpec (pair w) := by
  intro x fits
  let l : Column w → Bool := fun j => x (false,j)
  let r : Column w → Bool := fun j => x (true,j)
  let z := (pair w).eval x
  change (read (fun j => z (false,j)),read (fun j => z (true,j))) = absorb (read l) (read r)
  have test := merge_iff x fits
  change _ ↔ l (.inl false) = true ∧ r (.inl false) = true ∧ (parseRow l).compatible (parseRow r) at test
  cases hm : merge.eval ((loaded w).eval x) with
  | false =>
    have neg := mt test.mpr (by simp [hm])
    have h := identity_of_false x hm
    change z = x at h
    rw [h]
    exact (identity_absorb neg).symm
  | true =>
    obtain ⟨hl,hr,hc⟩ := test.mp hm
    have hb := fits true (parseRow r) (by change parseRow r ∈ read r; simp [read,hr])
    have hw := (Parsed.join_fits hc hb).1
    change word l 1 + (word l 2 + word r 2) < 2^w at hw
    have width := joined_width x hm (by change word l 2 + word r 2 < _; omega)
    have field (k : Fin 4) (h : k ≠ 2) : word (fun j => z (false,j)) k = word l k := by
      simp [z,pair,word,outputBit,h,rawWord,StatementCircuit.Expr.eval,saved,l]
    have enabled (t : Bool) : z (false,.inl t) = l (.inl t) := by
      cases t <;> simp [z,pair,outputBit,StatementCircuit.Expr.eval,saved,l]
    have disabled : z (true,.inl false) = false := by
      simp [z,pair,outputBit,hm,StatementCircuit.Expr.eval]
    change word (fun j => z (false,j)) 2 = word l 2 + word r 2 at width
    simp only [read,enabled,disabled,hl,hr,ite_true,Bool.false_eq_true,ite_false,absorb,hc]
    simp only [parseRow,Parsed.join,enabled,field 0 (by decide),field 1 (by decide),field 3 (by decide),width]

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
