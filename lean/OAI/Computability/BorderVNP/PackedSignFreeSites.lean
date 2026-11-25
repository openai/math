import OAI.Computability.BorderVNP.PackedSignFreeGrid
import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedBankSortedCell

/-! # Positive private factors after paid rounds and sorted cell-directory assembly -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
  InheritedProfile CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

omit [NeZero D] in
/-- A paid entry is stored by its genuine table position, so reading it contributes
the positive factor observation even if its eventual field value is zero. -/
theorem paid_signFree (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) :
    (PaidBox.tableFactor e position a v).SignFree := trivial

variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- Each physical paid site emits exactly its own one-copy position lookup. -/
theorem PaidSite.physical_signFree (symbol : S) (a : Fin e.count) (v : (e.net a).Site) :
    (PaidSite.physical e p bin perm positive first q symbol a v edgeID portID position).SignFree := by
  change ∀ fs ∈ [[PaidBox.tableFactor e position a v]], ∀ f ∈ fs, f.SignFree
  simpa only [List.forall_mem_singleton] using paid_signFree e position a v

/-- One actual shortening round keeps old site factors, inserts only the real paid
position table, and adds empty private directories for origins and terminals. -/
theorem roundSites_signFree (prior : ∀ v, (old v).SignFree) (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).SignFree := by
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact (prior v).retain _ _
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.SignFree
    simp
  · change ∀ fs ∈ ([] : List (List Factor)), ∀ f ∈ fs, f.SignFree
    simp
  · exact PaidSite.physical_signFree e p bin perm positive first q position edgeID portID a i v

/-- Every private table read by the final cell remains sign-free in the actual
stable public order, including cells whose filtered list of resident sites is empty. -/
theorem sortedDirectory_signFree {D ns ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
    (portID : P ↪ Fin np) (owner : Fin ns → ℕ) (state : N.Site → Site) (c : ℕ) (reports : List (List ℕ))
    (allSites : ∀ v, (state v).SignFree) :
    (FinalCell.directory owner N cell siteID edgeID portID state c reports).SignFree := by
  intro fs member f selected
  change fs ∈ (FinalCell.sites siteID owner c).flatMap (fun v => (state v).boxes) at member
  obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp member
  exact allSites v fs hv f selected

end Packing.Inherited

end BorderVNP
end Computability
end OAI
