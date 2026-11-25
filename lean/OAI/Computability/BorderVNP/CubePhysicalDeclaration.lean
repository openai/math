import OAI.Computability.BorderVNP.CubeDeclaration
import OAI.Computability.BorderVNP.CubePhysicalVertices
import OAI.Computability.BorderVNP.DiagonalCubeNetwork
import Mathlib.Data.Sym.Card

/-! # Declaring the pair rows for the selected physical cube packets

A packet contributes to the row indexed by the two symbols of its subcube
at the proposed grouping coordinate. A singleton contributes to the row of
its own two endpoint symbols, which can coincide. For each candidate cut
the count uses the actual selected edge widths, independently of the
proposed grouping. Consequently the declared least minimizer and every row
entry are uniquely forced on each passing computation path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP.MotifBase
open scoped Classical

variable {n d blocks K h : ℕ}

/-- Each entity to which one public declaration row is assigned. -/
abbrev Item (n d blocks width : ℕ) := Packet n d blocks ⊕ SingleSlot n d blocks width

/-- The unordered pair of groups for a packet or singleton. The diagonal
rows retain the singleton wires with co-located endpoint groups. -/
def itemRow {width : ℕ} (i : Fin (n+1)) : Item n d blocks width → Sym2 (Fin d)
  | .inl p => Sym2.mk (p.1.1 i).val.1 (p.1.1 i).val.2
  | .inr z => Sym2.mk (z.1.val.1 i) (z.1.val.2 i)

/-- The actual label of each cube vertex belongs to the packet's symbol row. -/
theorem vertex_mem_row {width : ℕ} (i : Fin (n+1)) (p : Packet n d blocks) (v : Vertex (n+1)) :
    vertexLabel p v i ∈ itemRow i (.inl p : Item n d blocks width) := by
  simp only [itemRow, Sym2.mem_iff, vertexLabel]
  split <;> simp

/-- Both original endpoint symbols of a singleton belong to its single assigned row. -/
theorem singleton_mem_row {width : ℕ} (i : Fin (n+1)) (z : SingleSlot n d blocks width) :
    z.1.val.1 i ∈ itemRow i (.inr z : Item n d blocks width) ∧
      z.1.val.2 i ∈ itemRow i (.inr z : Item n d blocks width) :=
  ⟨Sym2.mem_mk_left .., Sym2.mem_mk_right ..⟩

/-- A selected packet contributes precisely its internal edges in the cut
direction. A retained singleton contributes its one bit if its symbols differ. -/
def crossCount (b s : ℕ) (select : Packet n d blocks → Selector n K h) :
    Item n d blocks (h*b) → Fin (n+1) → ℕ
  | .inl p, j => ∑ v : Vertex (n+1), payload (onEdge s) (select p).2 (v,j)
  | .inr z, j => (decide (z.1.val.1 j ≠ z.1.val.2 j)).toNat

/-- Counting all internal cube edges whose placed labels differ gives the
packet's declared directional contribution. -/
theorem packet_crossCount (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (p : Packet n d blocks) (j : Fin (n+1)) :
    crossCount b s select (.inl p) j = ∑ e : Edge (n+1),
      if vertexLabel p (head e) j ≠ vertexLabel p e.1 j then payload (onEdge s) (select p).2 e else 0 := by
  simp [crossCount, vertexLabel_head_eq_iff, Fintype.sum_prod_type]

/-- Total actual width crossing a candidate coordinate. -/
def cutWidth (b s : ℕ) (select : Packet n d blocks → Selector n K h) (j : Fin (n+1)) : ℕ :=
  ∑ a : Item n d blocks (h*b), crossCount b s select a j

/-- The public tie-breaking choice of the first minimum directional width. -/
def chosen (b s : ℕ) (select : Packet n d blocks → Selector n K h) : Fin (n+1) :=
  firstMinimum (cutWidth b s select)

/-- Coordinate and all unordered symbol-pair row lengths advertised on the broadcast. -/
abbrev LengthDeclaration (n d : ℕ) :=
  Fin (n+1) × (Sym2 (Fin d) → Fin (n+1) → ℕ)

/-- The actual public checks for a profile's selected packet summands. -/
def passesLengths (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) : Prop :=
  passes itemRow (crossCount b s select) D

/-- The column totals of any proposed coordinate are independent of that
proposal and equal the actual number of crossing bits. -/
theorem sum_pair_lengths (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i j : Fin (n+1)) :
    (∑ r : Sym2 (Fin d), subtotals itemRow (crossCount b s select) i r j) =
      cutWidth b s select j :=
  sum_subtotals _ _ _ _

/-- The passing declaration has exactly the first minimum and the local rows
computed from the selected summands, including all same-symbol rows. -/
theorem passesLengths_iff (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) :
    passesLengths b s select D ↔
      D = (chosen b s select, subtotals itemRow (crossCount b s select) (chosen b s select)) := by
  constructor
  · rintro ⟨hrows,hmin⟩
    have hi : D.1 = chosen b s select := by
      simpa only [hrows,sum_pair_lengths,chosen] using hmin
    exact Prod.ext hi (by ext r j; rw [hrows,hi])
  · rintro rfl
    refine ⟨fun _ _ => rfl, ?_⟩
    simp only [sum_pair_lengths, chosen]

/-- For every tuple of packet selectors there is precisely one passing row
array and grouping coordinate. This does not change the number of paths. -/
theorem existsUnique_lengths (b s : ℕ) (select : Packet n d blocks → Selector n K h) :
    ∃! D : LengthDeclaration n d, passesLengths b s select D :=
  existsUnique_declaration _ _

/-- Every packet meets two different symbols in the proposed grouping, even
when its orientation is reversed or its selected internal width is zero. -/
theorem packet_row_not_diag {width : ℕ} (i : Fin (n+1)) (p : Packet n d blocks) :
    ¬(itemRow i (.inl p : Item n d blocks width)).IsDiag := by
  rw [itemRow, Sym2.mk_isDiag_iff]
  exact (p.1.1 i).property.ne

/-- A same-symbol declaration row has no bits crossing that grouping cut.
It can still contain local singleton slots or data. -/
theorem diagonal_row_width (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (r : Sym2 (Fin d)) (hr : r.IsDiag) :
    subtotals itemRow (crossCount b s select) i r i = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases he : itemRow i a = r
  · rw [ite_eq_left he]
    rw [← he] at hr
    cases a with
    | inl p => exact (packet_row_not_diag i p hr).elim
    | inr z =>
      rw [itemRow, Sym2.mk_isDiag_iff] at hr
      simp [crossCount,hr]
  · exact ite_eq_right he

/-- The length of the selector prefix in a pair's shared list. This depends on
the grouping coordinate and packet family but not on the actual selector words. -/
def rowSelectorBits (n d blocks K h : ℕ) (i : Fin (n+1)) (r : Sym2 (Fin d)) : ℕ :=
  ∑ p : Packet n d blocks, if itemRow i (.inl p : Item n d blocks 0) = r
    then VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h else 0

/-- Selector broadcasts occur only in off-diagonal symbol rows. -/
theorem diagonal_row_selectors (n d blocks K h : ℕ) (i : Fin (n+1)) (r : Sym2 (Fin d))
    (hr : r.IsDiag) : rowSelectorBits n d blocks K h i r = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right fun e => packet_row_not_diag i p (e ▸ hr)

/-- Summing the row selector lengths counts precisely one fixed-width selector
word per packet. -/
theorem sum_rowSelectorBits (n d blocks K h : ℕ) (i : Fin (n+1)) :
    (∑ r, rowSelectorBits n d blocks K h i r) =
      Fintype.card (Packet n d blocks) * VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h := by
  unfold rowSelectorBits
  rw [Finset.sum_comm]
  simp

/-- All local checks force every advertised row entry to fit inside its
physical column width. -/
theorem declared_entry_le (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (hp : passesLengths b s select D) (r : Sym2 (Fin d)) (j : Fin (n+1)) :
    D.2 r j ≤ cutWidth b s select j := by
  rw [hp.1 r j, ← sum_pair_lengths b s select D.1 j]
  exact Finset.single_le_sum (f := fun row => subtotals itemRow (crossCount b s select) D.1 row j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

/-- Attach the unique passing declaration to each original path. The path's
selector tuple determines all rows and the coordinate. Forgetting the
declaration is the exact inverse, even when several paths choose equal selectors. -/
def declareEquiv {A : Type*} (b s : ℕ) (selectors : A → Packet n d blocks → Selector n K h) :
    A ≃ ((a : A) × {D : LengthDeclaration n d // passesLengths b s (selectors a) D}) where
  toFun a := ⟨a, ⟨_, (passesLengths_iff b s (selectors a) _).mpr rfl⟩⟩
  invFun := Sigma.fst
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨a,D⟩
    exact congrArg (Sigma.mk a) (Subtype.ext ((passesLengths_iff _ _ _ _).mp D.property).symm)

end Cube.Physical

end BorderVNP
end Computability
end OAI
