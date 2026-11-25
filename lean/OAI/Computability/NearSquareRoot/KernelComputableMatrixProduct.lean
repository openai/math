import OAI.Computability.NearSquareRoot.KernelComputableMatrix
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Serial composition of encoded dyadic matrices

A product entry sums the products over every intermediate row and address.
All dimensions and both tables are ordinary input data for this evaluator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableMatrix

open KernelComputableDyadic

def product (rows inner cols : ℕ) (left right : Table) : Table :=
  make rows cols fun r c =>
    sum ((List.range inner).map fun j => mul (entry inner left r j) (entry cols right j c))

variable {X : Type*} [Primcodable X]

theorem primrec_product {rows inner cols : X → ℕ} {left right : X → Table}
    (hrows : Primrec rows) (hinner : Primrec inner) (hcols : Primrec cols)
    (hleft : Primrec left) (hright : Primrec right) :
    Primrec fun x => product (rows x) (inner x) (cols x) (left x) (right x) := by
  apply primrec_make hrows hcols
  apply primrec_sum.comp
  apply Primrec.list_map (Primrec.list_range.comp (hinner.comp Primrec.fst))
  unfold Primrec₂
  apply primrec_mul.comp
  · exact primrec_entry (hinner.comp (Primrec.fst.comp Primrec.fst))
      (hleft.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  · exact primrec_entry (hcols.comp (Primrec.fst.comp Primrec.fst))
      (hright.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))

set_option maxHeartbeats 800000 in
theorem computable_product {rows inner cols : X → ℕ} {left right : X → Table}
    (hrows : Computable rows) (hinner : Computable inner) (hcols : Computable cols)
    (hleft : Computable left) (hright : Computable right) :
    Computable fun x => product (rows x) (inner x) (cols x) (left x) (right x) := by
  let f (t : (ℕ × ℕ) × (ℕ × (Table × Table))) :=
    product t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2
  have hf : Primrec f := primrec_product
    (rows := fun t : (ℕ × ℕ) × (ℕ × (Table × Table)) => t.1.1)
    (inner := fun t => t.1.2) (cols := fun t => t.2.1)
    (left := fun t => t.2.2.1) (right := fun t => t.2.2.2)
    (Primrec.fst.comp .fst) (Primrec.snd.comp .fst) (Primrec.fst.comp .snd)
    (Primrec.fst.comp (Primrec.snd.comp .snd)) (Primrec.snd.comp (Primrec.snd.comp .snd))
  let args (x : X) := ((rows x,inner x),(cols x,(left x,right x)))
  have ha : Computable args := (hrows.pair hinner).pair (hcols.pair (hleft.pair hright))
  change Computable (fun x => f (args x))
  exact hf.to_comp.comp ha

private theorem range_sum (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Fin.sum_univ_castSucc, ih]

theorem value_entry_product {rows inner cols r c : ℕ} (left right : Table)
    (hr : r < rows) (hc : c < cols) :
    value (entry cols (product rows inner cols left right) r c) =
      ∑ j : Fin inner, value (entry inner left r j) * value (entry cols right j c) := by
  rw [product, entry_make _ hr hc, value_sum, List.map_map, range_sum]
  simp

/-- Matrix multiplication with arbitrary finite row and address numberings. -/
theorem represents_product {O J I : Type*} [Fintype J] {rows inner cols : ℕ}
    (eo : O ≃ Fin rows) (ej : J ≃ Fin inner) (ei : I ≃ Fin cols)
    (M : Matrix O J ℚ) (N : Matrix J I ℚ) (left right : Table)
    (hl : ∀ r j, value (entry inner left (eo r) (ej j)) = M r j)
    (hr : ∀ j c, value (entry cols right (ej j) (ei c)) = N j c) (r : O) (c : I) :
    value (entry cols (product rows inner cols left right) (eo r) (ei c)) = (M * N) r c := by
  rw [value_entry_product left right (eo r).isLt (ei c).isLt, Matrix.mul_apply]
  symm
  apply Fintype.sum_equiv ej
  intro j
  rw [hl, hr]

/-- Index of the corresponding pair in row-major order. The address
enumeration can be the native base-four address encoding at any width. -/
private def bankEquiv {Y : Type*} {n : ℕ} (b : ℕ) (e : Y ≃ Fin n) : Fin b × Y ≃ Fin (b*n) :=
  ((Equiv.refl (Fin b)).prodCongr e).trans finProdFinEquiv

private theorem bankEquiv_val {Y : Type*} {n b : ℕ} (e : Y ≃ Fin n) (p : Fin b × Y) :
    (bankEquiv b e p).val = p.1.val * n + (e p.2).val := by
  change (e p.2).val + n * p.1.val = _
  ac_rfl

/-- Row-bank form used by serial template instructions. The intermediate
matrix dimension is the number of work rows times the address count. -/
theorem represents_bank_product {Y : Type*} [Fintype Y] {rows inner cols n : ℕ} (e : Y ≃ Fin n)
    (M : Matrix (Fin rows × Y) (Fin inner × Y) ℚ) (N : Matrix (Fin inner × Y) (Fin cols × Y) ℚ)
    (left right : Table)
    (hl : Represents (inner*n) (bankIndex e) (bankIndex e) left M)
    (hr : Represents (cols*n) (bankIndex e) (bankIndex e) right N) :
    Represents (cols*n) (bankIndex e) (bankIndex e)
      (product (rows*n) (inner*n) (cols*n) left right) (M * N) := by
  intro r c
  simpa only [bankIndex, bankEquiv_val] using represents_product (bankEquiv rows e) (bankEquiv inner e)
    (bankEquiv cols e) M N left right (by simpa only [Represents, bankIndex, bankEquiv_val] using hl)
    (by simpa only [Represents, bankIndex, bankEquiv_val] using hr) r c

end KernelComputableMatrix

end NearSquareRoot
end Computability
end OAI
