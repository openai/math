import OAI.Computability.BorderVNP.CubeISALengthScan
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The row-array and coordinate checks on physical cube declarations

Unordered pairs use their smaller symbol first. A full array has one row
at each square-grid position and a zero row at every unused position below
the diagonal. A single local row can also be checked separately by the same code.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeLengths

open VPVNP.BurstRAM VPVNP.MotifBase Cube Cube.Physical

variable {n d : ℕ}

/-- Row-major ordinal, with the coordinate varying fastest. -/
def entryOrder (d a : ℕ) : (Fin d × Fin d) × Fin a ≃ Fin (d*d*a) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

/-- Ordinary word offset of the entry in the square symbol-pair table. -/
theorem entryOrder_val (s t : Fin d) (j : Fin (n+1)) :
    (entryOrder d (n+1) ((s,t),j)).val = (s.val*d+t.val)*(n+1)+j.val := by
  change j.val+(n+1)*(t.val+d*s.val) = _
  ac_rfl

/-- Image of an unordered-pair row array, including its zero padding. -/
def StoredRows (mem : ℕ → ℕ) (base : ℕ) (rows : Sym2 (Fin d) → Fin (n+1) → ℕ) : Prop :=
  ∀ (s t : Fin d) (j : Fin (n+1)), mem (base + (entryOrder d (n+1) ((s,t),j)).val) =
    if s ≤ t then rows (Sym2.mk s t) j else 0

/-- A word-by-word scan of the two dense arrays agrees precisely on the finite
unordered-pair declarations, including diagonal pairs and an empty alphabet. -/
theorem rowsAgree_iff (l : Layout) (mem : ℕ → ℕ) {actual claimed : Sym2 (Fin d) → Fin (n+1) → ℕ}
    (count : l.entries = d*d*(n+1)) (left : StoredRows mem l.actual actual)
    (right : StoredRows mem l.claimed claimed) :
    RowsAgree l mem ↔ ∀ r j, claimed r j = actual r j := by
  constructor
  · intro eq r j
    let p := Sym2.sortEquiv r
    let k := entryOrder d (n+1) (p.val,j)
    have hk : k.val < l.entries := by rw [count]; exact k.isLt
    have h := eq k.val hk
    have hr : Sym2.mk p.val.1 p.val.2 = r := Sym2.sortEquiv.symm_apply_apply r
    have a := left p.val.1 p.val.2 j
    have b := right p.val.1 p.val.2 j
    rw [ite_eq_left p.property,hr] at a b
    exact b.symm.trans (h.symm.trans a)
  · intro eq i hi
    have range : i < d*d*(n+1) := count ▸ hi
    obtain ⟨⟨⟨s,t⟩,j⟩,h⟩ := (entryOrder d (n+1)).surjective ⟨i,range⟩
    have e : (entryOrder d (n+1) ((s,t),j)).val = i := congrArg Fin.val h
    rw [← e,left,right,eq]

/-- On a single symbol row the local scan checks exactly its coordinate entries. -/
theorem localRowsAgree_iff (l : Layout) (mem : ℕ → ℕ) (actual claimed : Fin (n+1) → ℕ)
    (count : l.entries = n+1) (left : ∀ j : Fin (n+1), mem (l.actual+j.val) = actual j)
    (right : ∀ j : Fin (n+1), mem (l.claimed+j.val) = claimed j) :
    RowsAgree l mem ↔ ∀ j, claimed j = actual j := by
  constructor
  · intro h j
    simpa [left,right] using (h j.val (by rw [count]; exact j.isLt)).symm
  · intro h j hj
    let k : Fin (n+1) := ⟨j,count ▸ hj⟩
    exact (left k).trans ((h k).symm.trans (right k).symm)

variable {blocks K h : ℕ}

/-- The physical table stores the actual selector subtotals, the claimed rows and
the crossing counts of the selected packets and singleton wires. -/
structure PhysicalImage (l : Layout) (mem : ℕ → ℕ) (b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (D : LengthDeclaration n d) : Prop where
  /-- Number of entries in the full padded array. -/
  count : l.entries = d*d*(n+1)
  /-- Number of coordinates. -/
  dimension : l.coordinates = n+1
  /-- Coordinate word carried by the public declaration. -/
  coordinate : l.chosen = D.1.val
  /-- Row values recomputed from the actual packet and singleton contributions. -/
  actual : StoredRows mem l.actual (Cube.subtotals itemRow (crossCount b s select) D.1)
  /-- Advertised pair rows as addressed by the scan. -/
  claimed : StoredRows mem l.claimed D.2
  /-- Actual directional crossing counts. -/
  totals : ∀ j : Fin (n+1), mem (l.totals+j.val) = cutWidth b s select j

/-- The native equality and minimum tests are precisely the paper's passing
declaration predicate on its concrete physical table. -/
theorem PhysicalImage.passes {l : Layout} {mem : ℕ → ℕ} {b s : ℕ}
    {select : Packet n d blocks → Selector n K h} {D : LengthDeclaration n d}
    (image : PhysicalImage l mem b s select D) :
    RowsAgree l mem ∧ Least l mem ↔ passesLengths b s select D := by
  rw [rowsAgree_iff l mem image.count image.actual image.claimed,least_iff_first l mem image.dimension,
    image.coordinate, show (fun i : Fin (n+1) => mem (l.totals+i.val)) = cutWidth b s select from
      funext image.totals, Fin.val_inj]
  change _ ↔ (∀ r j, D.2 r j = Cube.subtotals itemRow (crossCount b s select) D.1 r j) ∧ _
  constructor <;> rintro ⟨row,minimal⟩ <;> refine ⟨row,?_⟩
  · simpa only [row,sum_pair_lengths] using minimal
  · simpa only [row,sum_pair_lengths] using minimal

/-- Full native verification of the physical declaration, with measured word
ticks, preservation of memory, and rejection of every incorrect declaration. -/
theorem physical_check_run {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (regs : Bank w) (m : Memory w) (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (fit : Fits w (readings pub) (readings m))
    (image : PhysicalImage (layout (readings pub) (readings m)) (readings m) b s select D) :
    TestRun pub mac check regs m
      (rowSetup.slots + (d*d*(n+1))*(rowBody.slots+1)+1 +
       (minSetup.slots+pivot.slots+(n+1)*(minBody.slots+1)+2))
      (passesLengths b s select D) (Kept (readings regs) (readings m)) :=
  (check_run regs m fit).mono (by rw [image.count,image.dimension]) image.passes (fun _ hp => hp)

end RoutingISA.CubeLengths

end BorderVNP
end Computability
end OAI
