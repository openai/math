import OAI.Computability.BorderVNP.DiagonalPins
import OAI.Computability.BorderVNP.ResidueEntryFieldGuess
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.Computability.QuantumFactoring.BitNumbers

/-!
# Checked bit guard for padded residue pins

A pin arrives as individual little-endian binary fields. The fixed advice
checks the basis address, the signed time exponent and all nonnegative
parameter exponents. No table of the exponentially many pins is needed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM.Pins

open Diagonal ResiduePins ResidueEntryField ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork
open ExactQuantumFactoring.BitArithmetic VPVNP.RAMSerialization

variable {h w β H : ℕ}

/-- Retrieve a chosen field of the packed pin directly from its contiguous wires. -/
def field (i : Fin (h+2)) : BooleanNetwork ((h+2)*w) w :=
  select (fun j => finProdFinEquiv (i,j))

/-- The little-endian Boolean word value is exactly the word decoded by the pin codec. -/
theorem field_value (i : Fin (h+2)) (b : Fin ((h+2)*w) → Bool) :
    value ((field i).eval b) = ((arrayBits (h+2) w).symm b i).val := by
  let a := (arrayBits (h+2) w).symm b
  have hbits : (field i).eval b = fun j => (a i).val.testBit j.val := by
    funext j
    rw [VPVNP.LiveHeader.testBit_wordBits]
    change b (finProdFinEquiv (i,j)) = wordBits w (a i) j
    rw [← arrayBits_at a i j]
    exact (congrFun ((arrayBits (h+2) w).apply_symm_apply b) _).symm
  exact hbits ▸ bitsValue_ofFn (a i)

/-- The range guard for an address works even when every bit pattern is legal,
and rejects the empty-basis case. -/
def basisCheck (h w β : ℕ) : BooleanNetwork ((h+2)*w) 1 :=
  if β = 0 then constant false else wordLe (field 0) (literal _ w (β-1))

/-- A parameter coordinate is shifted by H, so its word is in the closed interval [H,2H]. -/
def coordinate (w H : ℕ) (j : Fin h) : BooleanNetwork ((h+2)*w) 1 :=
  (wordLe (literal _ w H) (field j.succ.succ)).band
    (wordLe (field j.succ.succ) (literal _ w (2*H)))

/-- Complete range guard for one actual external pin field. -/
def guard (h w β H : ℕ) : BooleanNetwork ((h+2)*w) 1 :=
  (basisCheck h w β).band ((wordLe (field 1) (literal _ w (2*H))).band
    (all (List.ofFn (coordinate w H : Fin h → _))))

private theorem literal_value {n a w : ℕ} (ha : a < 2^w) (b : Basis n) :
    (bitsValue ((literal n w a).eval b)).toNat = a := by
  rw [literal,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha]

/-- The actual bit guard accepts exactly the words that decode to box indices,
including the zero padding outside the allowed matrix dimension. -/
theorem guard_correct (hβ : β ≤ 2^w) (hH : 2*H < 2^w) (b : Fin ((h+2)*w) → Bool) :
    (guard h w β H).eval b 0 = true ↔ ((boxPinCodec h hβ hH).decode b).isSome = true := by
  rw [boxPinCodec_decode_isSome_iff]
  let a := (arrayBits (h+2) w).symm b
  have vb (i : Fin (h+2)) : (bitsValue ((field i).eval b)).toNat = (a i).val := field_value i b
  have hb : (basisCheck h w β).eval b 0 = true ↔ (a 0).val < β := by
    by_cases zero : β = 0
    · simp [basisCheck,zero]
    · simp [basisCheck,zero,wordLe_eval,vb,literal_value (show β-1<2^w by omega)]
      omega
  simp only [guard,eval_band,Bool.and_eq_true,hb,wordLe_eval,vb,literal_value hH,
    decide_eq_true_eq, all_eval, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    coordinate, literal_value (show H<2^w by omega), within, a]

/-- The Boolean node count is linear in the number of coordinates and in the pin word width. -/
theorem guard_count (h w β H : ℕ) : (guard h w β H).net.count ≤ (h+3)*(100*w+25) := by
  have lit (a) : (literal ((h+2)*w) w a).net.count = w := wordConstant_count _
  have fld (i : Fin (h+2)) : (field (w := w) i).net.count = 0 := rfl
  have hb : (basisCheck h w β).net.count ≤ 49*w+9 := by
    by_cases hz : β=0
    · unfold basisCheck
      rw [ite_eq_left hz]
      simp
    · unfold basisCheck
      rw [ite_eq_right hz]
      have bound := wordLe_count (field (h := h) (w := w) 0) (literal _ w (β-1))
      simp only [lit,fld] at bound
      omega
  have hwc (j : Fin h) : (coordinate w H j).net.count ≤ 98*w+19 := by
    have ha := wordLe_count (literal ((h+2)*w) w H) (field j.succ.succ)
    have hb := wordLe_count (field j.succ.succ) (literal ((h+2)*w) w (2*H))
    simp only [coordinate,count_band,lit,fld] at ha hb ⊢
    omega
  have ht := wordLe_count (field (h := h) (w := w) 1) (literal _ w (2*H))
  have hall := all_count (List.ofFn (coordinate w H : Fin h → _)) (c := 98*w+19)
    (by intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc; exact hwc j)
  simp only [guard,count_band,lit,fld,List.length_ofFn] at ht hall ⊢
  nlinarith

end DiagonalResidueRAM.Pins

end BorderVNP
end Computability
end OAI
