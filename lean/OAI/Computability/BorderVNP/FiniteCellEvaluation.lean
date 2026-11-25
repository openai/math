import OAI.Computability.BorderVNP.FiniteCellCounts

/-! # Exact physical field factors on cells of the substituted input network

A fixed tuple of original cable and port bits determines one passing report per
cell, even when a selected entry vanishes. Summing over these reported words
recovers the complete local tensor product. Partitioning sites by their actual
cell labels gives the original network contraction after summing the shared wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory

open Crossing CellSparse
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Field F] [Fintype F]

/-- Signed sparse validation followed by deterministic finite-field output. -/
noncomputable def scan (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : N.Assignment) (x : Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) : F :=
  let B := directory N sites table w
  let z := bank N a x (tail N w c)
  let counts := fun i : Fin B.reportedCounts.length => B.reportedCounts[i].map z
  (B.weight z : F) * FieldStack.productPaths (FieldPowers.program (scalar N sites table w))
      FieldPowers.factor (fun _ => 1) (1 + ∑ i, (2*(counts i).length+2)) (.visit (Fin.last _)) counts

/-- Sum over every possible report without changing the field weight or the
number of choices of the underlying cable assignment. -/
theorem sum_scan (sites : List N.Site) (table : N.Tables F) (w : ℕ) (fits : sites.length < 2^w)
    (a : N.Assignment) (x : Ports bits) :
    (∑ c, scan N sites table w a x c) = (sites.map (N.read table a x)).prod := by
  obtain ⟨chosen,ok,uniq⟩ := unique_claims N sites table w fits a x
  let good (c : Fin (Fintype.card F) → Fin w → Bool) := ∀ j,
    (ids N sites table a x).count j.val = ((VPVNP.RAMSerialization.wordBits w).symm (c j)).val
  have eqc c : good c ↔ c = chosen := ⟨fun h => uniq c ((countsValid_iff ..).mpr h),
    fun h => h ▸ (countsValid_iff ..).mp ok⟩
  have val c : scan N sites table w a x c = if c = chosen then (sites.map (N.read table a x)).prod else 0 := by
    have h := scan_claims N sites table w a x c
    change scan N sites table w a x c = if good c then _ else 0 at h
    simpa only [eqc] using h
  simp [val]

variable {Cell : Type} [Fintype Cell] (cell : N.Site → Cell)

/-- Choose an order on the sites actually assigned to this cell, as permitted
in the nonuniform literal description of the proposed network. -/
noncomputable def siteList (v : Cell) : List N.Site :=
  List.ofFn fun i : Fin (Fintype.card {s : N.Site // cell s = v}) =>
    ((Fintype.equivFin {s : N.Site // cell s = v}).symm i).val

omit [Fintype P] [Fintype F] [Fintype Cell] in
private theorem siteList_prod (table : N.Tables F) (a : N.Assignment) (x : Ports bits) (v : Cell) :
    ((siteList N cell v).map (N.read table a x)).prod = ∏ s : {s : N.Site // cell s = v}, N.read table a x s.val := by
  rw [siteList,List.map_ofFn,List.prod_ofFn]
  exact (Fintype.equivFin {s : N.Site // cell s = v}).symm.prod_comp (fun s => N.read table a x s.val)

omit [Fintype Cell] in
/-- Each cell has exactly one successful tuple at the logarithmic field width
chosen from the number of its actual sites. -/
theorem sum_scan_cell (table : N.Tables F) (a : N.Assignment) (x : Ports bits) (v : Cell) :
    let w := Nat.clog 2 ((siteList N cell v).length+1)
    (∑ c, scan N (siteList N cell v) table w a x c) = ∏ s : {s : N.Site // cell s = v}, N.read table a x s.val := by
  intro w
  exact (sum_scan N _ _ w (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)) _ _).trans
    (siteList_prod N cell table a x v)

/-- The exact input bit-network tensor, as the product of physically checked
cell scalars summed over the independent original internal cable words. -/
theorem value_by_cells (table : N.Tables F) (x : Ports bits) :
    N.value table x = ∑ a : N.Assignment, ∏ v : Cell,
      let sites := siteList N cell v
      ∑ c, scan N sites table (Nat.clog 2 (sites.length+1)) a x c := by
  unfold Network.value
  apply Finset.sum_congr rfl
  intro a _
  rw [← Fintype.prod_fiberwise cell (N.read table a x)]
  exact Finset.prod_congr rfl fun v _ => (sum_scan_cell N cell table a x v).symm

end FieldDirectory

end BorderVNP
end Computability
end OAI
