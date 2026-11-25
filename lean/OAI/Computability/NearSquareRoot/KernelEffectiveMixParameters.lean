import OAI.Computability.NearSquareRoot.KernelPassComputablePacked
import OAI.Computability.NearSquareRoot.KernelPassMix

/-! # Source parameters for a compiled row of dyadic coefficients

The row ruler and the magnitudes of its integer weights are primitive
recursive functions of the literal opcode and the row and column numbers.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveMix

open IntegerMultiplication KernelPass KernelPass.ComputableSyntax KernelPassMix
open KernelComputableDyadic

set_option maxHeartbeats 900000

abbrev Row := Op × ℕ
abbrev Entry := Row × ℕ

def raw (t : Entry) : KernelComputableDyadic.Code :=
  t.1.1.2.2.getD (t.1.2 * arg t.1.1 0 + t.2) KernelComputableDyadic.zero

def coeff (op : Op) (b : Fin (arg op 1)) (a : Fin (arg op 0)) : Coefficient :=
  KernelComputableDyadic.coefficient (raw ((op,b.val),a.val))

theorem primrec_raw : Primrec raw := by
  have op : Primrec (fun t : Entry => t.1.1) := Primrec.fst.comp Primrec.fst
  exact (Primrec.list_getD KernelComputableDyadic.zero).comp ((Primrec.snd.comp Primrec.snd).comp op)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst)
      (primrec_arg.comp op (.const 0))) Primrec.snd)

def prefixDenom (r : Row) : ℕ → ℕ
  | 0 => 0
  | n+1 => max (raw (r,n)).2 (prefixDenom r n)

theorem primrec_prefixDenom : Primrec₂ prefixDenom := by
  have hs : Primrec₂ (fun r : Row => fun v : ℕ × ℕ => max (raw (r,v.1)).2 v.2) :=
    Primrec.nat_max.comp (Primrec.snd.comp (primrec_raw.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))) (Primrec.snd.comp Primrec.snd)
  refine (Primrec.nat_rec (Primrec.const 0) hs).of_eq ?_
  intro r n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (max (raw (r,n)).2) ih

def rowDenom (r : Row) : ℕ := prefixDenom r (arg r.1 0)

theorem primrec_rowDenom : Primrec rowDenom :=
  primrec_prefixDenom.comp Primrec.id (primrec_arg.comp Primrec.fst (.const 0))

private theorem prefixDenom_eq (r : Row) (n : ℕ) :
    prefixDenom r n = (Finset.range n).sup fun j => (raw (r,j)).2 := by
  induction n with
  | zero => simp [prefixDenom]
  | succ n ih => rw [prefixDenom, ih, Finset.range_add_one, Finset.sup_insert]

def rowCoeff (r : Row) (j : Fin (arg r.1 0)) : Coefficient :=
  KernelComputableDyadic.coefficient (raw (r,j.val))

theorem rowDenom_eq_raw (r : Row) :
    rowDenom r = denom (rowCoeff r) := by
  rw [rowDenom, prefixDenom_eq, denom]
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact Finset.le_sup (f := fun k => (rowCoeff r k).2)
      (Finset.mem_univ (⟨j,Finset.mem_range.mp hj⟩ : Fin (arg r.1 0)))
  · apply Finset.sup_le
    intro j _
    exact Finset.le_sup (f := fun j => (raw (r,j)).2)
      (Finset.mem_range.mpr j.isLt)

theorem rowDenom_eq (op : Op) (b : Fin (arg op 1)) :
    rowDenom (op,b.val) = denom (coeff op b) := rowDenom_eq_raw _

def negative (t : Entry) : Prop := (raw t).1.1 < (raw t).1.2

instance (t : Entry) : Decidable (negative t) := Nat.decLt _ _

theorem primrec_negative : PrimrecPred negative :=
  Primrec.nat_lt.comp ((Primrec.fst.comp Primrec.fst).comp primrec_raw)
    ((Primrec.snd.comp Primrec.fst).comp primrec_raw)

def weightMagnitude (t : Entry) : ℕ :=
  let u := (raw t).1
  (u.1 - u.2 + (u.2 - u.1)) * 2^(rowDenom t.1 - (raw t).2)

theorem primrec_weightMagnitude : Primrec weightMagnitude := by
  have hp := (Primrec.fst.comp Primrec.fst).comp primrec_raw
  have hn := (Primrec.snd.comp Primrec.fst).comp primrec_raw
  exact Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.nat_sub.comp hp hn)
    (Primrec.nat_sub.comp hn hp)) (Generator.primrecNatPow.comp (.const 2)
    (Primrec.nat_sub.comp (primrec_rowDenom.comp Primrec.fst) (Primrec.snd.comp primrec_raw)))

theorem numerator_eq_weight (t : Entry) :
    numerator (rowDenom t.1) (KernelComputableDyadic.coefficient (raw t)) =
      if negative t then -(weightMagnitude t : ℤ) else (weightMagnitude t : ℤ) := by
  let a := (raw t).1.1
  let b := (raw t).1.2
  let d := rowDenom t.1 - (raw t).2
  split_ifs with h
  · change a < b at h
    change ((a : ℤ)-b) * 2^d = -(((a-b + (b-a)) * 2^d : ℕ) : ℤ)
    push_cast
    rw [show (a : ℤ)-b = -((a-b : ℕ) + (b-a : ℕ) : ℤ) by omega]
    ring
  · change ¬a < b at h
    change ((a : ℤ)-b) * 2^d = (((a-b + (b-a)) * 2^d : ℕ) : ℤ)
    push_cast
    rw [show (a : ℤ)-b = ((a-b : ℕ) + (b-a : ℕ) : ℤ) by omega]

theorem signedScale_weight (t : Entry) (s : Grid.S) :
    signedScale (numerator (rowDenom t.1) (KernelComputableDyadic.coefficient (raw t))) s =
      if negative t then Grid.neg (natScale (weightMagnitude t) s)
      else natScale (weightMagnitude t) s := by
  rw [numerator_eq_weight]
  by_cases h : negative t
  · simp only [h, ↓reduceIte]
    have pos : 0 < weightMagnitude t := by
      have h' := h
      change (raw t).1.1 < (raw t).1.2 at h'
      unfold weightMagnitude
      exact Nat.mul_pos (by omega) (pow_pos (by decide) _)
    cases n : weightMagnitude t with
    | zero => omega
    | succ n => rfl
  · simp only [h, ↓reduceIte]
    rfl

end EffectiveMix

end NearSquareRoot
end Computability
end OAI
