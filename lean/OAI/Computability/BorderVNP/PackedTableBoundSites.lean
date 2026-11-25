import OAI.Computability.BorderVNP.PackedTableBoundGrid
import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # A fixed table bound across actual paid rounds and final merged cell directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
  InheritedProfile CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Only the finitely many site types of the fixed paid identity enter this bound.
The constant eight includes the original degree-three gates and all staged unary rows. -/
noncomputable def tableLimit : ℕ := max 8 (Finset.univ.sup fun a : Fin e.count =>
  Finset.univ.sup fun v : (e.net a).Site => max (PaidBox.arity e a v) (2^PaidBox.arity e a v))

omit [NeZero D] in
/-- Every paid box stores exactly one copy of its fixed table, independently of its
repetition count, numeric position IDs and later cell placement. -/
theorem paid_tableBound (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) :
    (PaidBox.tableFactor e position a v).TableBound (tableLimit e) := by
  apply factor_mono (CellBox.factor_tableBound (e.net a) (PaidBox.ids e position a) v (PaidBox.laneOrder (e.net a) v) Fin.val)
  apply le_trans _ (le_max_right ..)
  exact (Finset.le_sup (s := Finset.univ) (f := fun z : (e.net a).Site => max (PaidBox.arity e a z) (2^PaidBox.arity e a z)) (Finset.mem_univ v)).trans
    (Finset.le_sup (s := Finset.univ) (f := fun b : Fin e.count => Finset.univ.sup fun z : (e.net b).Site =>
      max (PaidBox.arity e b z) (2^PaidBox.arity e b z)) (Finset.mem_univ a))

omit [NeZero D] in
/-- The same fixed template bound covers the initial routed grid. -/
theorem Site.TableBound.of_eight {s : Site} (h : s.TableBound 8) : s.TableBound (tableLimit e) :=
  fun fs hs f hf => factor_mono (h fs hs f hf) (le_max_left ..)

variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- One real shortening step transports all prior tables and inserts only the fixed
paid boxes. Origin and terminal histogram, shuffle and hook data are public records. -/
theorem roundSites_tableBound (prior : ∀ v, (old v).TableBound (tableLimit e)) (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).TableBound (tableLimit e) := by
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact prior v
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.TableBound _
    simp
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.TableBound _
    simp
  · change ∀ fs ∈ [[PaidBox.tableFactor e position i v]], ∀ f ∈ fs, f.TableBound _
    simpa only [List.forall_mem_singleton] using paid_tableBound e position i v

end Packing.Inherited

namespace Packing.Inherited

open Crossing CellSparse
open scoped Classical

/-- The final stable per-cell merge preserves the table dimensions of all resident
sites. The actual relocated sparse records and report links do not alter the boxes. -/
theorem sortedDirectory_tableBound {D ns ne np M : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
    (portID : P ↪ Fin np) (owner : Fin ns → ℕ) (state : N.Site → Site) (c : ℕ) (reports : List (List ℕ))
    (localBounds : ∀ v, (state v).TableBound M) :
    ∀ fs ∈ (FinalCell.directory owner N cell siteID edgeID portID state c reports).boxes, ∀ f ∈ fs, f.TableBound M := by
  intro fs h
  change fs ∈ (FinalCell.sites siteID owner c).flatMap (fun v => (state v).boxes) at h
  obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp h
  exact localBounds v fs hv

end Packing.Inherited

end BorderVNP
end Computability
end OAI
