import OAI.Computability.BorderVNP.FiniteLocalCell
import OAI.Computability.BorderVNP.FiniteCellCopiesContraction

/-! # Sparse finite-field scans on the actual one-cell network

The private wire bank contains exactly the internal cable words of this cell.
The crossing and original external words are supplied at its boundary. One
joint tuple of reported field multiplicities is summed for the whole bundle.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteLocalCell
open Crossing FieldDirectory
open scoped BigOperators Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {Cell : Type} [Fintype Cell] [DecidableEq Cell] (cell : N.Site → Cell) (c : Cell)

/-- The physical enumeration of every actual fine site inside this one public cell. -/
noncomputable def siteList : List (network N cell c).Site :=
  List.ofFn (Fintype.equivFin (network N cell c).Site).symm

omit [Fintype P] [Fintype Cell] in
/-- Site enumeration includes every local factor once, including when there are none. -/
theorem siteList_prod {A : Type*} [CommMonoid A] (f : (network N cell c).Site → A) :
    ((siteList N cell c).map f).prod = ∏ s, f s := by
  rw [siteList, List.map_ofFn, List.prod_ofFn]
  exact (Fintype.equivFin (network N cell c).Site).symm.prod_comp f

variable {F : Type*} [Field F] [Fintype F]
  (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (table : N.Tables F)

/-- At fixed boundary data, summing both the private wire assignments and the
literal finite-field report recovers the exact entry of the cell's tensor. -/
theorem sum_scan_cellTables (a : ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (x : ∀ p : External N cell c, Fin (bits p.val) → Bool) :
    let sites := siteList N cell c
    let w := Nat.clog 2 (sites.length + 1)
    (∑ z : (network N cell c).Assignment, ∑ report : Fin (Fintype.card F) → Fin w → Bool,
      FieldDirectory.scan (network N cell c) sites (tables N cell c table) w z (ports N cell c a x) report) =
      N.cellTables cell position table c a x := by
  dsimp only
  rw [← value_eq_cellTables N cell c position table a x]
  unfold Network.value
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro z _
  exact (FieldDirectory.sum_scan _ _ _ _ (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)) z _).trans
    (siteList_prod N cell c _)

/-- Repeated copies share one physical directory and a single set of subtotal
words. Summing those words and all independent private assignments recovers
the product of the original cell entries on their supplied boundary data. -/
theorem sum_copies_scan_cellTables {copies : ℕ}
    (a : Fin copies → ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (x : Fin copies → ∀ p : External N cell c, Fin (bits p.val) → Bool) :
    let sites := siteList N cell c
    let w := Nat.clog 2 (copies * sites.length + 1)
    (∑ z : Fin copies → (network N cell c).Assignment, ∑ report : Fin (Fintype.card F) → Fin w → Bool,
      Copies.scan (network N cell c) sites (tables N cell c table) w z
        (fun i => ports N cell c (a i) (x i)) report) =
      ∏ i : Fin copies, N.cellTables cell position table c (a i) (x i) := by
  dsimp only
  let M := network N cell c
  let T := tables N cell c table
  let X (i : Fin copies) := ports N cell c (a i) (x i)
  let f (i : Fin copies) (z : M.Assignment) := ∏ v : M.Site, M.read T z (X i) v
  calc
    _ = ∑ z : Fin copies → M.Assignment, ∏ i : Fin copies, f i (z i) := by
      apply Finset.sum_congr (Finset.ext fun _ => by simp)
      intro z _
      exact (Copies.sum_scan M _ T z X).trans (Finset.prod_congr rfl fun i _ => siteList_prod N cell c _)
    _ = ∏ i : Fin copies, ∑ z : M.Assignment, f i z := (Fintype.prod_sum f).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← value_eq_cellTables N cell c position table (a i) (x i)]
      unfold Network.value
      apply Finset.sum_congr (Finset.ext fun _ => by simp)
      intro z _
      apply Finset.prod_congr (Finset.ext fun _ => by simp)
      intro v _
      rfl

end FiniteLocalCell

end BorderVNP
end Computability
end OAI
