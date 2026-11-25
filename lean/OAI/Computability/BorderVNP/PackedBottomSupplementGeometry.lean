import OAI.Computability.BorderVNP.PackedBottomReportCursors
import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.PackedRetainedWork

/-! # Supplemental use-record endpoints in the actual retained cell slabs

A bottom bundle is retained at an injective final host. Its initial copy-major
work prefix fits inside that host's present work. Thus its report endpoints
stay in the canonical private-wire bank, and the combined expanded use widths
of an owned cell are charged once to distinct retained site slabs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing Inherited CellAddresses
open scoped Classical

variable {D : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ}
variable (M : Network D P bits) (cell : M.Site → ℕ) (program : M.Site → Site)
variable {s : ℕ} (siteID : M.Site ↪ Fin s) (host : J ↪ M.Site)
variable (bundle : J → Bundle)

/-- A site's final physical slab contains the old box at its original offset zero. -/
def RetainedOperands : Prop :=
  ∀ j, (bundle j).header.boxBase =
      siteBase M cell (cell (host j)) siteID (fun v => (program v).size) ⟨host j,rfl⟩ ∧
    ∃ birth : Site, (bundle j).header.copies*(bundle j).header.stride = birth.work ∧
      Nonempty (birth.Retention (program (host j)))

variable (operands : RetainedOperands M cell program siteID host bundle)

include operands

omit [Fintype P] [Fintype J] in
/-- Each complete bottom box ends inside its final cell's genuine private-wire part,
after transport through an arbitrary sequence of actual retention layers. -/
theorem retained_box_end (j : J) :
    (bundle j).header.boxBase+(bundle j).header.copies*(bundle j).header.stride ≤
      guessedSize M cell (cell (host j)) + siteSize M cell (cell (host j)) (fun v => (program v).size) := by
  obtain ⟨base,birth,work,⟨retention⟩⟩ := operands j
  have old := retention.work_le
  have small : birth.work ≤ (program (host j)).size :=
    old.trans (Nat.le_add_right _ _)
  rw [base,work]
  exact (Nat.add_le_add_left small _).trans (siteBase_fits M cell _ siteID _ ⟨host j,rfl⟩)

omit [Fintype P] [Fintype J] in
/-- Every scalar address emitted for a staged report or the zero suffix fits the
private-wire bound, including the endpoint of an empty suffix. -/
theorem retained_report_scalar (j : J) (rank : ℕ) (hr : rank ≤ (bundle j).header.cap)
    (stride : (bundle j).header.stride = bottomStride (bundle j).header.orig (bundle j).header.cap)
    (copies : 0 < (bundle j).header.copies) :
    (bundle j).header.boxBase+(bundle j).header.orig+rank ≤
      guessedSize M cell (cell (host j)) + siteSize M cell (cell (host j)) (fun v => (program v).size) := by
  have one := Nat.mul_le_mul_right (bundle j).header.stride copies
  rw [Nat.one_mul] at one
  have h : (bundle j).header.orig+rank ≤ (bundle j).header.stride := by
    rw [stride]
    exact Nat.add_le_add_left hr _
  rw [Nat.add_assoc]
  exact (Nat.add_le_add_left (h.trans one) _).trans (retained_box_end M cell program siteID host bundle operands j)

/-- The exact owner sublist in its native stable order, indexed by its original name. -/
abbrev Owned (c : ℕ) := {j : J // cell (host j) = c}

/-- Inject an owned original into the real final cell's own site directory. -/
def ownerSite (c : ℕ) : Owned M cell host c ↪ {v : M.Site // cell v = c} where
  toFun j := ⟨host j.val,j.property⟩
  inj' _ _ h := Subtype.ext (host.injective (congrArg Subtype.val h))

omit operands in
private theorem embedding_sum {I U : Type} [Fintype I] [Fintype U] (e : I ↪ U) (f : U → ℕ) :
    ∑ i, f (e i) ≤ ∑ j, f j := by
  rw [← Finset.sum_map Finset.univ e f]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [Fintype P] in
/-- Summing copy-major reservations over all owned origins charges each true retained
site once, and only once, to this cell's actual site-storage budget. -/
theorem owned_work_le (c : ℕ) :
    (∑ j : Owned M cell host c, (bundle j.val).header.copies*(bundle j.val).header.stride) ≤
      siteSize M cell c (fun v => (program v).size) := by
  let f := fun v : {v : M.Site // cell v = c} => (program v.val).size
  have one (j : Owned M cell host c) :
      (bundle j.val).header.copies*(bundle j.val).header.stride ≤ f (ownerSite M cell host c j) := by
    obtain ⟨birth,hb,⟨retention⟩⟩ := (operands j.val).2
    rw [hb]
    exact retention.work_le.trans (Nat.le_add_right _ _)
  refine (Finset.sum_le_sum (fun j _ => one j)).trans ?_
  have bound := embedding_sum (ownerSite M cell host c) f
  refine bound.trans_eq ?_
  unfold siteSize
  apply Finset.sum_congr _ (fun _ _ => rfl)
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

omit [Fintype P] in
/-- Both the actual chosen use-bit stream and every zero suffix fit inside the
expanded initial reservations of the owned true sites. -/
theorem owned_report_le (c : ℕ)
    (cap : ∀ j, count (bundle j).factors ≤ (bundle j).header.cap)
    (stride : ∀ j, (bundle j).header.stride = bottomStride (bundle j).header.orig (bundle j).header.cap) :
    (∑ j : Owned M cell host c, (bundle j.val).useBits) ≤
      ∑ j : Owned M cell host c, (bundle j.val).header.copies*(bundle j.val).header.cap ∧
    (∑ j : Owned M cell host c, (bundle j.val).header.copies*(bundle j.val).header.cap) ≤
      siteSize M cell c (fun v => (program v).size) := by
  constructor
  · apply Finset.sum_le_sum
    intro j _
    rw [Bundle.useBits,Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (cap j.val)
  · refine (Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left (bundle j.val).header.copies
      ((Nat.le_add_left _ _).trans_eq (stride j.val).symm))).trans
      (owned_work_le M cell program siteID host bundle operands c)

omit [Fintype P] operands in
/-- The number of row-count headers is at most the number of retained fine sites
of the cell even when all their immutable private sidecars are empty. -/
theorem owned_card_le (c : ℕ) :
    Fintype.card (Owned M cell host c) ≤ Fintype.card {v : M.Site // cell v = c} :=
  Fintype.card_le_of_injective (ownerSite M cell host c) (ownerSite M cell host c).injective

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
