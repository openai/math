import OAI.Computability.BorderVNP.PackedBottomGridRowSize
import OAI.Computability.BorderVNP.PackedFinalCellRowBounds
import OAI.Computability.BorderVNP.PackedTableBoundSites

/-! # Public and private row bounds fixed by one paid crossing identity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing CellSparse Shortening Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The row shapes needed by the actual packet compiler. Their two size
constants depend only on the chosen paid identity. -/
def Site.CompilerRows (s : Site) : Prop :=
  s.Schema ∧ s.RowBound (16*(e.count+1)) ∧ s.TableBound (tableLimit e)

/-- The degree-three initial table and scalar bottom row bounds instantiate
the joint invariant for any fixed paid identity. -/
theorem Site.CompilerRows.of_initial {s : Site} (h : s.Schema) (hr : s.RowBound 9) (ht : s.TableBound 8) :
    s.CompilerRows e :=
  ⟨h,fun r hx => (hr r hx).trans (by omega),Site.TableBound.of_eight e ht⟩

variable [NeZero D] {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- One actual crossing transition preserves the joint compiler bounds,
including the histogram checks, the newly born paid sites, and all staged
old inputs. -/
theorem roundSites_compilerRows (h : ∀ v, (old v).CompilerRows e)
    (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).CompilerRows e :=
  ⟨roundSites_schema e p bin perm positive first q binName position siteID edgeID portID old cuts (fun j => (h j).1) v,
   roundSites_rowBound e p bin perm positive first q binName position siteID edgeID portID old cuts le_rfl
     (fun j => (h j).2.1) v,
   roundSites_tableBound e p bin perm positive first q binName position siteID edgeID portID old cuts
     (fun j => (h j).2.2) v⟩

end Packing.Inherited

end BorderVNP
end Computability
end OAI
