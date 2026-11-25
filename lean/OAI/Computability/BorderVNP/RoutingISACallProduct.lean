import OAI.Computability.BorderVNP.RoutingISACallAccounting
import OAI.Computability.BorderVNP.RoutingISACallProof
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Summing the actual signed paths at owned cells

The finite choice set of a private routine supplies one factor per owned row.
The full instruction trace is injective in those choices. Thus the sum of the
products of the signs over distinct complete RAM histories is the product of
the individual private path sums.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ}

/-- An optional row outcome contributes one for a skipped cell, and its returned sign otherwise. -/
def outcomeValue : Option Outcome → ℤ
  | none => 1
  | some o => o.2.value

/-- Give a list a head element while keeping both factors recoverable. -/
private def prependEmb {α : Type*} : α × List α ↪ List α :=
  ⟨fun (x,xs) => x :: xs, fun ⟨_,_⟩ ⟨_,_⟩ e => Prod.ext (List.cons.inj e).1 (List.cons.inj e).2⟩

private theorem prepend_apply {α : Type*} (x : α) (xs : List α) : prependEmb (x,xs) = x::xs := rfl

/-- Cartesian products of the independent, row-indexed choices. -/
def rowProducts (rows : ℕ → Finset (Option Outcome)) : ℕ → ℕ → Finset (List (Option Outcome))
  | _, 0 => {[]}
  | i, n+1 => (rows i ×ˢ rowProducts rows (i+1) n).map prependEmb

/-- Choices for this row come from the installed macro on its actual arguments. -/
def Frame.rowOptions (f : Frame) (m : Memory w) (choices : List (Word w) → Finset Outcome)
    (i : ℕ) : Finset (Option Outcome) :=
  if (m (f.address i)).val = f.team then
    if (m (f.address i+1)).val + (m (f.address i+2)).val ≤ 2^w then
      (choices (TeamRAM.previous m (f.burst m i))).map ⟨some, Option.some_injective _⟩
    else ∅
  else {none}

private theorem row_mem {f : Frame} {m : Memory w} {choices : List (Word w) → Finset Outcome}
    {macros : TeamOpcode.Macros w 8} (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2)
    (i : ℕ) (x : Option Outcome) : x ∈ f.rowOptions m choices i ↔ f.Valid m macros i x := by
  unfold Frame.rowOptions Frame.Valid
  split
  · split
    · rename_i fits
      cases x <;> simp [spec,fits,eq_comm]
    · simp_all
  · simp

/-- The product enumeration gives all and only the native row outcomes for the chosen interval. -/
theorem Frame.mem_rowProducts {f : Frame} {m : Memory w} {choices : List (Word w) → Finset Outcome}
    {macros : TeamOpcode.Macros w 8} (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2)
    (i n : ℕ) (xs : List (Option Outcome)) :
    xs ∈ rowProducts (f.rowOptions m choices) i n ↔ xs.length = n ∧ f.Admitted m macros i xs := by
  induction n generalizing i xs with
  | zero =>
    cases xs <;> simp [rowProducts,Admitted]
  | succ n ih =>
    cases xs <;> simp [rowProducts, prepend_apply, Finset.mem_product, row_mem spec, ih,
      Admitted, and_left_comm, and_assoc, and_comm]

/-- The sum of the products factors as the product of the row sums. -/
theorem sum_rowProducts (rows : ℕ → Finset (Option Outcome)) (i n : ℕ) :
    ∑ xs ∈ rowProducts rows i n, (xs.map outcomeValue).prod =
      ((List.range' i n).map fun j => ∑ x ∈ rows j, outcomeValue x).prod := by
  induction n generalizing i with
  | zero => simp [rowProducts]
  | succ n ih =>
    simp only [rowProducts, Finset.sum_map, prepend_apply,
      Finset.sum_product, List.map_cons, List.prod_cons, ← Finset.mul_sum, ih,
      ← Finset.sum_mul, List.range'_succ]

/-- Enumerate the actual chronological directory traces as a finite set. -/
noncomputable def Frame.histories (f : Frame) (pub : Arg → Word w) (m : Memory w)
    (choices : List (Word w) → Finset Outcome) : Finset (List (TeamRAM.Event w)) := by
  classical
  exact (rowProducts (f.rowOptions m choices) 0 f.count).image
    (fun xs => setupTrace pub m ++ f.scanTrace m 0 xs)

/-- These finite histories are precisely the accepting executions of the actual directory,
including the exact input choice tape. -/
theorem Frame.mem_histories {pub : Arg → Word w} {m : Memory w} {s : Bank w}
    {choices : List (Word w) → Finset Outcome} {macros : TeamOpcode.Macros w 8}
    (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w)
    (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (es : List (TeamRAM.Event w)) :
    es ∈ (Frame.ofMemory pub m).histories pub m choices ↔
      TeamRAM.execute (callOwnedCells.program.fetch pub macros) ⟨0,s⟩ m
        (es.map TeamRAM.Event.choices) = some es := by
  classical
  rw [histories, Finset.mem_image, execute_directory_iff frameFit room, and_iff_right rfl]
  constructor
  · rintro ⟨xs,hx,rfl⟩
    obtain ⟨len,ad⟩ := (mem_rowProducts spec ..).1 hx
    refine ⟨xs,⟨len,ad,rfl⟩,?_⟩
    rintro ys ⟨ly,ay,eq⟩
    exact scanTrace_inj _ _ _ ay ad (ly.trans len.symm) (List.append_cancel_left eq.symm)
  · rintro ⟨xs,⟨len,ad,he⟩,_⟩
    exact ⟨xs,(mem_rowProducts spec ..).2 ⟨len,ad⟩,he.symm⟩

private theorem opt_prod (xs : List (Option Outcome)) :
    ((xs.filterMap id).map (TeamRAM.Sign.value ∘ Prod.snd)).prod = (xs.map outcomeValue).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [outcomeValue] at ih ⊢ <;> first | exact ih | exact Or.inl ih

/-- The sum of actual native history weights is exactly the product of the per-row
path sums, with the canonical unit value on skipped cells. -/
theorem Frame.sum_histories {pub : Arg → Word w} {f : Frame} {m : Memory w}
    {choices : List (Word w) → Finset Outcome} {macros : TeamOpcode.Macros w 8}
    (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2) :
    ∑ es ∈ f.histories pub m choices, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((List.range' 0 f.count).map fun i => ∑ x ∈ f.rowOptions m choices i, outcomeValue x).prod := by
  classical
  rw [histories, Finset.sum_image]
  · simp_rw [directory_weight, opt_prod]
    exact sum_rowProducts ..
  · intro x hx y hy e
    have a := (mem_rowProducts spec ..).1 hx
    have b := (mem_rowProducts spec ..).1 hy
    exact scanTrace_inj _ _ _ a.2 b.2 (a.1.trans b.1.symm) (List.append_cancel_left e)

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
