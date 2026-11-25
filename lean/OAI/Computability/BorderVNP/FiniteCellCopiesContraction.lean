import OAI.Computability.BorderVNP.FiniteCellCopiesScan

/-! # Cellwise tensor contraction with shared site directories

At an original cell, every bottom copy uses the same literal site table.
Reindexing the independent internal wires and the actual assigned site lists
expresses the complete tensor power by one joint checked report per cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory.Copies

open Crossing
open scoped BigOperators Classical
open private siteList_prod from OAI.Computability.BorderVNP.FiniteCellEvaluation

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Field F] [Fintype F] {copies : ℕ}

omit [Field F] in
/-- A degree-three site contributes its table once, even when the copy count is zero.
The expanded visit count determines only the width of the scalar reports. -/
theorem directory_layout (sites : List N.Site) (table : N.Tables F) (copies w : ℕ) :
    (directory N sites table copies w).boxes = [sites.map (factor N table)] ∧
    (directory N sites table copies w).records = [.box 0 0 copies (Fintype.card (Wire N))] ∧
    ((directory N sites table copies w).reportedCounts.map List.length).sum = Fintype.card F * w := by
  simp [directory,List.map_ofFn,Function.comp_def]

omit [Field F] in
/-- Every reported bit lies below the total linear lane bank plus the joint report
width, independent of the number of times any literal table is visited. -/
theorem claimAddress_lt (copies w : ℕ) (v : Fin (Fintype.card F)) (i : Fin w) :
    claimAddress N copies w v i < width N copies + Fintype.card F*w :=
  by simpa only [claimAddress,Nat.mul_comm w (Fintype.card F)] using Nat.add_lt_add_left (finProdFinEquiv (i,v)).isLt (width N copies)

variable {Cell : Type} [Fintype Cell] (cell : N.Site → Cell)

omit [Fintype Cell] in
/-- One joint report at a cell recovers the entries on exactly that cell's actual sites. -/
theorem sum_scan_cell (table : N.Tables F) (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (v : Cell) :
    let sites := siteList N cell v
    (∑ c, scan N sites table (Nat.clog 2 (copies*sites.length+1)) a x c) =
      ∏ i : Fin copies, ∏ s : {s : N.Site // cell s = v}, N.read table (a i) (x i) s.val := by
  intro sites
  rw [sum_scan]
  exact Finset.prod_congr rfl fun i _ => siteList_prod N cell table (a i) (x i) v

/-- The complete tensor power on independent external ports, summed over the actual
internal cable assignments with exactly one physically checked count tuple per cell. -/
theorem value_by_cells (table : N.Tables F) (x : Fin copies → Ports bits) :
    (∏ i : Fin copies, N.value table (x i)) =
      ∑ a : Fin copies → N.Assignment, ∏ v : Cell,
        let sites := siteList N cell v
        ∑ c, scan N sites table (Nat.clog 2 (copies*sites.length+1)) a x c := by
  unfold Network.value
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∏ i : Fin copies, ∏ v : Cell, ∏ s : {s : N.Site // cell s = v}, N.read table (a i) (x i) s.val :=
      Finset.prod_congr rfl fun i _ => (Fintype.prod_fiberwise cell (N.read table (a i) (x i))).symm
    _ = ∏ v : Cell, ∏ i : Fin copies, ∏ s : {s : N.Site // cell s = v}, N.read table (a i) (x i) s.val :=
      Finset.prod_comm
    _ = _ := Finset.prod_congr rfl fun v _ => (sum_scan_cell N cell table a x v).symm

end FieldDirectory.Copies

end BorderVNP
end Computability
end OAI
