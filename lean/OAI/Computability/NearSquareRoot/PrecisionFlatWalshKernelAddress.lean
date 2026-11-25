import OAI.Computability.NearSquareRoot.KernelScaleLayout
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Bit positions in the physical Walsh kernel's active ordinal

The selector serializes lane, column, and pair bit in that order, from most
significant to least significant. Reversing this ordinal gives its position
for natural-number bit tests.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshKernel

open IntegerMultiplication KernelSelectorAlign KernelScaleStream KernelScaleLayout

/-- The physical bit position of a kernel lane, column and pair bit. -/
def slots (a h : ℕ) : (Fin (a+1) × (Fin h × Fin 2)) ≃ Fin ((a+1)*(2*h)) :=
  ((Equiv.prodCongr (Equiv.refl _) (finProdFinEquiv.trans (finCongr (Nat.mul_comm h 2)))).trans
    finProdFinEquiv).trans Fin.revPerm

private theorem value_testBit (s : List Bool) (i : ℕ) (hi : i < s.length) :
    (Bits.value s).testBit i = s[i] := by
  induction s generalizing i with
  | nil => simp at hi
  | cons b s ih =>
    have hv : Bits.value (b::s) = Nat.bit b (Bits.value s) := by
      cases b <;> simp [Bits.value_cons, Nat.bit_val, Nat.add_comm]
    rw [hv]
    cases i with
    | zero => simp
    | succ i => simpa only [Nat.testBit_bit_succ, List.getElem_cons_succ] using ih i (by simpa using hi)

private theorem flat_get (a : ℕ) (cs : List (Column a)) (j : Fin (a+1)) (i : ℕ) (hi : i < cs.length) :
    (flatBits a cs)[j.val*cs.length+i]? = cs[i]?.map (fun c => KernelSelectorAlign.get a c j) := by
  induction a with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    simp [flatBits, bitStreams, KernelSelectorAlign.get]
  | succ a ih =>
    change ((cs.map Prod.fst) ++ flatBits a (cs.map Prod.snd))[_]? = _
    refine Fin.cases ?_ (fun r => ?_) j
    · simp [List.getElem?_append_left, hi, KernelSelectorAlign.get]
    · have hi' : i < (cs.map Prod.snd).length := by simpa using hi
      have hbound : (cs.map Prod.fst).length ≤ r.succ.val*cs.length+i := by
        simp only [List.length_map, Fin.val_succ, Nat.succ_mul]
        omega
      rw [List.getElem?_append_right hbound]
      have he : r.succ.val*cs.length+i-(cs.map Prod.fst).length = r.val*cs.length+i := by
        simp only [List.length_map, Fin.val_succ, Nat.succ_mul]
        omega
      rw [he]
      simpa [KernelSelectorAlign.get, Function.comp_def] using ih (cs.map Prod.snd) r hi'

private theorem single_len {a h : ℕ} (x : KernelPass.Addr (a+1) h) :
    (singleColumns (List.ofFn x)).length = 2*h := by
  simp [singleColumns, List.length_flatMap, Function.comp_def, Nat.mul_comm]

private theorem pairBound {h : ℕ} (t : Fin h) (b : Fin 2) : 2*t.val+b.val < 2*h := by omega

private theorem single_get {a h : ℕ} (x : KernelPass.Addr (a+1) h) (t : Fin h) (b : Fin 2) :
    (singleColumns (List.ofFn x))[2*t.val+b.val]? = some (split a (x t) b) := by
  induction h with
  | zero => exact Fin.elim0 t
  | succ h ih =>
    rw [List.ofFn_succ]
    change (split a (x 0) 0 :: split a (x 0) 1 :: singleColumns (List.ofFn (Fin.tail x)))[_]? = _
    refine Fin.cases ?_ (fun r => ?_) t
    · fin_cases b <;> rfl
    · change (_ :: _ :: _)[2*(r.val+1)+b.val]? = _
      rw [show 2*(r.val+1)+b.val = (2*r.val+b.val)+2 by omega]
      simpa only [List.getElem?_cons_succ, Fin.tail] using ih (Fin.tail x) r

/-- Reading a bit of the natural-number rank recovers its corresponding
binary kernel coordinate, including the little-endian reversal. -/
theorem testBit_rank {a h : ℕ} (x : KernelPass.Addr (a+1) h) (j : Fin (a+1))
    (t : Fin h) (b : Fin 2) :
    (rank x).val.testBit (slots a h (j,t,b)).val = decide (x t j b = 1) := by
  let cs := singleColumns (List.ofFn x)
  let word := flatBits a cs
  let m := j.val*(2*h)+(2*t.val+b.val)
  have hc : cs.length = 2*h := single_len x
  have hl : word.length = (a+1)*(2*h) := by simp [word, hc]
  have hm : m < (a+1)*(2*h) := by
    have := Nat.mul_le_mul_right (2*h) j.isLt
    rw [Nat.succ_mul] at this
    have := pairBound t b
    dsimp [m]
    omega
  have hs : (slots a h (j,t,b)).val = (a+1)*(2*h)-1-m := by
    simp [slots, Fin.rev, m, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
    omega
  change (bitValue word).testBit _ = _
  rw [endianness, value_testBit _ _ (by rw [List.length_reverse, hl]; exact (slots a h (j,t,b)).isLt),
    List.getElem_reverse]
  have hidx : word.length-1-(slots a h (j,t,b)).val = j.val*cs.length+(2*t.val+b.val) := by
    rw [hl, hs, hc]
    dsimp [m] at *
    omega
  have hi : 2*t.val+b.val < cs.length := by rw [hc]; exact pairBound t b
  have result := flat_get a cs j (2*t.val+b.val) hi
  rw [show cs[2*t.val+b.val]? = _ from single_get x t b] at result
  simp only [Option.map_some, split, KernelSelectorAlign.get_ofFn] at result
  have hj : j.val*cs.length+(2*t.val+b.val) < word.length := by simpa only [hl,hc] using hm
  rw [List.getElem?_eq_getElem hj] at result
  simpa only [hidx] using Option.some.inj result

end FlatWalshKernel

end NearSquareRoot
end Computability
end OAI
