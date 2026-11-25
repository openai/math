import OAI.Computability.NearSquareRoot.KernelComputableMatrix
import OAI.Computability.NearSquareRoot.KernelPass

/-! # Parallel row-bank composition on encoded dyadic matrices

A parallel plan concatenates the row banks, while retaining the same address
numbering inside each row. Its matrix has two diagonal blocks whose strides
are the sizes of the corresponding input banks. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableMatrix

open KernelComputableDyadic

/-- Assemble a direct sum, with all four dimensions measured in scalar entries. -/
def block (rowsL rowsR colsL colsR : ℕ) (x y : Table) : Table :=
  make (rowsL + rowsR) (colsL + colsR) fun r c =>
    if r < rowsL then (if c < colsL then entry colsL x r c else zero)
    else if c < colsL then zero else entry colsR y (r - rowsL) (c - colsL)

@[simp] theorem block_length (o u i j : ℕ) (xs ys : Table) :
    (block o u i j xs ys).length = (o+u)*(i+j) := make_length ..

variable {α : Type*} [Primcodable α]

theorem primrec_block {o u i j : α → ℕ} {xs ys : α → Table}
    (ho : Primrec o) (hu : Primrec u) (hi : Primrec i) (hj : Primrec j)
    (hx : Primrec xs) (hy : Primrec ys) :
    Primrec fun a => block (o a) (u a) (i a) (j a) (xs a) (ys a) := by
  unfold block
  apply primrec_make (Primrec.nat_add.comp ho hu) (Primrec.nat_add.comp hi hj)
  have hr : Primrec (fun p : α × ℕ × ℕ => p.2.1) := Primrec.fst.comp .snd
  have hc : Primrec (fun p : α × ℕ × ℕ => p.2.2) := Primrec.snd.comp .snd
  exact Primrec.ite (Primrec.nat_lt.comp hr (ho.comp .fst))
    (Primrec.ite (Primrec.nat_lt.comp hc (hi.comp .fst))
      (primrec_entry (hi.comp .fst) (hx.comp .fst) hr hc) (.const zero))
    (Primrec.ite (Primrec.nat_lt.comp hc (hi.comp .fst)) (.const zero)
      (primrec_entry (hj.comp .fst) (hy.comp .fst)
        (Primrec.nat_sub.comp hr (ho.comp .fst)) (Primrec.nat_sub.comp hc (hi.comp .fst))))

theorem computable_block {o u i j : α → ℕ} {xs ys : α → Table}
    (ho : Computable o) (hu : Computable u) (hi : Computable i) (hj : Computable j)
    (hx : Computable xs) (hy : Computable ys) :
    Computable fun a => block (o a) (u a) (i a) (j a) (xs a) (ys a) := by
  have h : Primrec fun p : ((ℕ × ℕ) × (ℕ × ℕ)) × (Table × Table) =>
      block p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2.1 p.2.2 :=
    primrec_block (Primrec.fst.comp (Primrec.fst.comp .fst)) (Primrec.snd.comp (Primrec.fst.comp .fst))
      (Primrec.fst.comp (Primrec.snd.comp .fst)) (Primrec.snd.comp (Primrec.snd.comp .fst)) (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)
  exact h.to_comp.comp (((ho.pair hu).pair (hi.pair hj)).pair (hx.pair hy))

private theorem slot_lt {k n : ℕ} (r : Fin k) (v : Fin n) : r.val*n + v.val < k*n :=
  calc
    r.val*n + v.val < r.val*n + n := Nat.add_lt_add_left v.isLt _
    _ = (r.val+1)*n := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ r.isLt

/-- The row-major direct sum implements the parallel node for each in-range address.
The address code may be any numbering shared by its two children. -/
theorem block_represents {o u i j n : ℕ} {X : Type} (address : X → Fin n)
    (xs ys : Table) (M : Matrix (Fin o × X) (Fin i × X) ℚ)
    (N : Matrix (Fin u × X) (Fin j × X) ℚ)
    (hm : Represents (i*n) (bankIndex address) (bankIndex address) xs M)
    (hn : Represents (j*n) (bankIndex address) (bankIndex address) ys N) :
    Represents ((i+j)*n) (bankIndex address) (bankIndex address) (block (o*n) (u*n) (i*n) (j*n) xs ys) (KernelPass.directSum M N) := by
  rintro ⟨r,y⟩ ⟨c,x⟩
  simp only [bankIndex]
  have hrow := slot_lt r (address y)
  have hcol := slot_lt c (address x)
  rw [Nat.add_mul] at hrow hcol ⊢
  rw [block, entry_make _ hrow hcol]
  clear hrow hcol
  cases r using Fin.addCases <;> cases c using Fin.addCases <;> rename_i a b
  · simpa [KernelPass.directSum, bankIndex, slot_lt a (address y), slot_lt b (address x)] using hm (a,y) (b,x)
  · simp [KernelPass.directSum, slot_lt a (address y), Nat.add_mul, Nat.add_assoc]
  · simp [KernelPass.directSum, slot_lt b (address x), Nat.add_mul, Nat.add_assoc]
  · simpa [KernelPass.directSum, bankIndex, Nat.add_mul, Nat.add_assoc] using hn (a,y) (b,x)

end KernelComputableMatrix

end NearSquareRoot
end Computability
end OAI
