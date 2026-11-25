import OAI.ThreeFlat.Diagonal.CompressorNodeIncident
import OAI.ThreeFlat.Diagonal.CompressorDemandEval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Bit semantics of the two incident-record masks -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr
open scoped BigOperators Fin.CommRing

def pattern {n : ℕ} (p : Fin n → Bool) : ℕ := ∑ i : Fin n, if p i then 2^i.val else 0

theorem pattern_last {n : ℕ} (p : Fin (n+1) → Bool) :
    pattern p = pattern (fun i : Fin n => p i.castSucc) + (if p (Fin.last n) then 2^n else 0) := by
  rw [pattern,Fin.sum_univ_castSucc]
  rfl

theorem pattern_lt {n : ℕ} (p : Fin n → Bool) : pattern p < 2^n := by
  induction n with
  | zero => simp [pattern]
  | succ n ih =>
    have lo := ih (fun i : Fin n => p i.castSucc)
    rw [pattern_last,pow_succ]
    split <;> omega

theorem pattern_bit {n : ℕ} (p : Fin n → Bool) (i : Fin n) :
    (pattern p).testBit i.val = p i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pattern_last]
      have lo := Nat.testBit_lt_two_pow (pattern_lt (fun i : Fin n => p i.castSucc))
      cases h : p (Fin.last n) <;>
        simp [Nat.add_comm,Nat.testBit_two_pow_add_eq,lo]
    · rw [pattern_last]
      have bit := ih (fun i : Fin n => p i.castSucc) j
      cases h : p (Fin.last n) <;>
        simp [Nat.add_comm,Nat.testBit_two_pow_add_gt j.isLt,bit]

theorem pattern_zero_iff {n : ℕ} (p : Fin n → Bool) : pattern p=0 ↔ ∀ i,p i=false := by
  constructor
  · intro h i
    rw [←pattern_bit p i,h,Nat.zero_testBit]
  · intro h
    simp [pattern,h]

variable {w : ℕ} (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value data mem vs

theorem mask_value {n : ℕ} (a : Fin n → F) (p : Fin n → Bool)
    (hp : ∀ i, V (a i)=1 ↔ p i=true) :
    V (mask a)=(pattern p : Word w) := by
  rw [mask,Demand.totals_word,List.map_map,←Fin.sum_univ_def,pattern,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i=true <;> simp [Formula.value,RAM.DescriptorExpr.Comparison.test,
    Fin.ofNat_eq_cast,hp,h]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
