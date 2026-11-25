import OAI.Computability.BorderVNP.PackedTableBoundSites
import OAI.Computability.BorderVNP.PackedFieldBoundGrid
import OAI.Computability.BorderVNP.PackedBankPacketFields

/-! # Independent local address and global identifier bounds after placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

omit [NeZero D] in
/-- A paid table's actual key addresses are bounded by the fixed paid identity.
Only the binary global directory positions use the separate identifier bound. -/
theorem paid_splitFields (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) {V U : ℕ}
    (localCap : tableLimit e ≤ V) (ids : ∀ z, position z ≤ U) :
    (PaidBox.tableFactor e position a v).FieldBound V ∧ (PaidBox.tableFactor e position a v).IDBound U := by
  have tab := factor_mono (paid_tableBound e position a v) localCap
  simp only [Factor.TableBound,PaidBox.tableFactor,CellBox.factor,CellBox.rows,List.length_ofFn] at tab
  simp only [Factor.FieldBound,Factor.TableBound,Factor.IDBound,PaidBox.tableFactor,CellBox.factor,CellBox.rows,
    List.length_ofFn,List.forall_mem_ofFn_iff]
  exact ⟨⟨tab,fun i => i.isLt.le.trans tab.1⟩,fun _ => ids _⟩

variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- Transport the independent bounds through all actual constructors of a geometric
shortening stage. Record relocation and copy count affect neither stored field. -/
theorem roundSites_splitFields {V U : ℕ} (localCap : tableLimit e ≤ V) (ids : ∀ z, position z ≤ U)
    (prior : ∀ v, (old v).SplitFields V U) (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).SplitFields V U := by
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact prior v
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.FieldBound _ ∧ f.IDBound _
    simp
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.FieldBound _ ∧ f.IDBound _
    simp
  · change ∀ fs ∈ [[PaidBox.tableFactor e position i v]], ∀ f ∈ fs, f.FieldBound V ∧ f.IDBound U
    simpa only [List.forall_mem_singleton] using paid_splitFields e position i v localCap ids

/-- The final true compiler directory preserves both relative fields and the original
global paid-table identifiers through its stable table merge. -/
theorem sortedDirectory_splitFields {dim ns₁ ne₁ np₁ V U : ℕ} {P₁ : Type*} [Fintype P₁] {widths : P₁ → ℕ}
    (N : Network dim P₁ widths) (cell : N.Site → ℕ) (sites : N.Site ↪ Fin ns₁) (edges : N.Edge ↪ Fin ne₁)
    (ports : P₁ ↪ Fin np₁) (owner : Fin ns₁ → ℕ) (state : N.Site → Site) (c : ℕ) (reports : List (List ℕ))
    (bounds : ∀ v, (state v).SplitFields V U) :
    ∀ fs ∈ (FinalCell.directory owner N cell sites edges ports state c reports).boxes,
      ∀ f ∈ fs, f.FieldBound V ∧ f.IDBound U := by
  intro fs h
  change fs ∈ (FinalCell.sites sites owner c).flatMap (fun v => (state v).boxes) at h
  obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp h
  exact bounds v fs hv

end Packing.Inherited

end BorderVNP
end Computability
end OAI
