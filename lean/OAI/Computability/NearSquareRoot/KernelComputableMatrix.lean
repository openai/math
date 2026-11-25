import OAI.Computability.NearSquareRoot.KernelComputableDyadic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

/-! # Primitive-recursive dense dyadic matrix tables

Entries are numbered row by row. The tabulator and the consumer take their
dimensions as inputs, so the same computation handles all bank and address
sizes appearing in a finite template certificate. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableMatrix

abbrev Scalar := KernelComputableDyadic.Code
abbrev Table := List Scalar

/-- Read a row and column in the supplied row-major storage. -/
def entry (cols : ℕ) (t : Table) (r c : ℕ) : Scalar :=
  t.getD (r*cols+c) KernelComputableDyadic.zero

/-- Materialize all entries in order, including the empty rectangular cases. -/
def make (rows cols : ℕ) (f : ℕ → ℕ → Scalar) : Table :=
  (List.range (rows*cols)).map (fun k => f (k/cols) (k%cols))

@[simp] theorem make_length (rows cols : ℕ) (f : ℕ → ℕ → Scalar) :
    (make rows cols f).length = rows*cols := by simp [make]

theorem entry_make {rows cols r c : ℕ} (f : ℕ → ℕ → Scalar) (hr : r < rows) (hc : c < cols) :
    entry cols (make rows cols f) r c = f r c := by
  have hidx : r*cols+c < rows*cols := by
    calc
      r*cols+c < (r+1)*cols := by simpa only [Nat.succ_mul] using Nat.add_lt_add_left hc (r*cols)
      _ ≤ _ := Nat.mul_le_mul_right cols hr
  rw [entry, List.getD_eq_getElem _ _ (by simpa using hidx)]
  simp [make, Nat.mod_eq_of_lt hc]
  rw [Nat.mul_comm r cols, Nat.mul_add_div (by omega : 0 < cols), Nat.div_eq_of_lt hc, Nat.add_zero]

/-- Interpret a rectangular table using the row and column address enumerations. -/
def Represents {O I : Type*} (cols : ℕ) (out : O → ℕ) (inp : I → ℕ) (t : Table)
    (M : Matrix O I ℚ) : Prop :=
  ∀ i j, KernelComputableDyadic.value (entry cols t (out i) (inp j)) = M i j

def bankIndex {r n : ℕ} {X : Type*} (addr : X → Fin n) (p : Fin r × X) : ℕ :=
  p.1.val*n + (addr p.2).val

variable {α : Type*} [Primcodable α]

theorem primrec_entry {cols r c : α → ℕ} {t : α → Table}
    (hcols : Primrec cols) (ht : Primrec t) (hr : Primrec r) (hc : Primrec c) :
    Primrec fun a => entry (cols a) (t a) (r a) (c a) :=
  (Primrec.list_getD KernelComputableDyadic.zero).comp ht
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hr hcols) hc)

theorem primrec_make {rows cols : α → ℕ} {f : α → ℕ → ℕ → Scalar}
    (hr : Primrec rows) (hc : Primrec cols)
    (hf : Primrec fun p : α × ℕ × ℕ => f p.1 p.2.1 p.2.2) :
    Primrec fun a => make (rows a) (cols a) (f a) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hr hc))
    (hf.comp (Primrec.fst.pair ((Primrec.nat_div.comp Primrec.snd (hc.comp Primrec.fst)).pair
      (Primrec.nat_mod.comp Primrec.snd (hc.comp Primrec.fst))))).to₂

theorem computable_entry {cols r c : α → ℕ} {t : α → Table}
    (hcols : Computable cols) (ht : Computable t) (hr : Computable r) (hc : Computable c) :
    Computable fun a => entry (cols a) (t a) (r a) (c a) :=
  (Primrec.list_getD KernelComputableDyadic.zero).to_comp.comp ht
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp hr hcols) hc)

/-- Tabulation also accepts an arbitrary total recursive entry algorithm. -/
theorem computable_make {rows cols : α → ℕ} {f : α → ℕ → ℕ → Scalar}
    (hr : Computable rows) (hc : Computable cols)
    (hf : Computable fun p : α × ℕ × ℕ => f p.1 p.2.1 p.2.2) :
    Computable fun a => make (rows a) (cols a) (f a) := by
  let atIndex (a : α) (k : ℕ) := f a (k/cols a) (k%cols a)
  have hq : Computable (fun p : α × ℕ => p.2/cols p.1) :=
    Primrec.nat_div.to_comp.comp Computable.snd (hc.comp Computable.fst)
  have hm : Computable (fun p : α × ℕ => p.2%cols p.1) :=
    Primrec.nat_mod.to_comp.comp Computable.snd (hc.comp Computable.fst)
  have he : Computable₂ atIndex := (hf.comp (Computable.fst.pair (hq.pair hm))).to₂
  let step (a : α) (k : ℕ × Table) := k.2 ++ [atIndex a k.1]
  have he' : Computable (fun p : α × ℕ × Table => atIndex p.1 p.2.1) :=
    he.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hs : Computable₂ step := (Primrec.list_concat.to_comp.comp
    (Computable.snd.comp Computable.snd) he').to₂
  apply (Computable.nat_rec (Primrec.nat_mul.to_comp.comp hr hc) (Computable.const []) hs).of_eq
  intro a
  change Nat.rec [] (fun k xs => step a (k,xs)) _ = (List.range _).map (atIndex a)
  induction rows a * cols a with
  | zero => rfl
  | succ k ih => simp [step, List.range_succ, ih]

end KernelComputableMatrix

end NearSquareRoot
end Computability
end OAI
