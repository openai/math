import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedBankProfileWidths

/-! # Local box references and selector widths throughout a physical round

Retaining a history adds only equalities. The origin and terminal use fixed
selector widths with the actual histogram alphabet. A new paid box references
its single local table at ordinal zero. These facts supply the preconditions of
the final merged directory and its private profile checker.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse Crossing Shortening Shortening.CombiningStep Shortening.StaticRows
  BankPacket BankJoint InheritedProfile
open scoped Classical
open private origin_blocks terminal_blocks from OAI.Computability.BorderVNP.PackedBankMergeCharges

/-- Every stored reference names an existing site-local box, and every profile
has a selector width admitted by the private compiler. -/
def Site.Schema (s : Site) : Prop :=
  ∀ r ∈ s.rows, r.BoxRefFits s.boxes.length ∧ r.ProfileWidthOK

private theorem refs_of_empty (boxes : List (List Factor)) (rs : List Record)
    (empty : Directory.resolvedRows boxes rs = []) (r : Record) (hr : r ∈ rs) :
    r.BoxRefFits boxes.length := by
  cases r with
  | box i b c st =>
    have hm : (⟨b,c,st,boxes.getD i []⟩ : BoxBlock) ∈ Directory.resolvedRows boxes rs :=
      List.mem_filterMap.mpr ⟨_,hr,rfl⟩
    rw [empty] at hm
    cases hm
  | _ => exact trivial

/-- The inherited cut list consists solely of equalities, so local references
and profile widths keep their certified bounds. -/
theorem Site.schema_retain (s : Site) (hs : s.Schema) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).Schema := by
  intro r hr
  rw [s.retain_rows,List.mem_append] at hr
  rcases hr with hr | hr
  · exact hs r hr
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨trivial,trivial⟩

/-- A public box prefix and an absolute bit base keep every stored row well
formed in the larger merged directory. -/
theorem Site.schema_placed (s : Site) (hs : s.Schema) (off base total : ℕ)
    (span : base+s.boxes.length ≤ total) (r : Record) (hr : r ∈ s.placedRows off base) :
    r.BoxRefFits total ∧ r.ProfileWidthOK := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  obtain ⟨hb,hw⟩ := hs t ht
  have h1 : (t.shift off).BoxRefFits s.boxes.length := by cases t <;> exact hb
  have h2 : (t.shift off).ProfileWidthOK := (t.profileWidthOK_shift off).mpr hw
  refine ⟨Record.rebaseBox_refFits _ h1 span,?_⟩
  cases t <;> exact h2

namespace PaidSite

/-- The born paid box points to its sole one-copy table. All its other rows are
physical wire ties, for every multiplicity, including zero. -/
theorem born_schema {n : ℕ} (w : Fin n → ℕ) (c input : ℕ) (starts : Fin n → ℕ) (f : Factor) :
    (born w c input starts f).Schema := by
  intro r hr
  change r ∈ (born w c input starts f).directory.records at hr
  rw [directory] at hr
  change r ∈ (Paid.rows w).map (RecordCode.read (PaidBinding.fields w c 0 0 (source w c starts))) at hr
  rw [Paid.read_rows,PaidBox.decode,List.map_append,List.mem_append] at hr
  rcases hr with hr | hr
  · rw [List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact ⟨trivial,trivial⟩
    · simp only [List.map_cons,List.map_nil,List.mem_singleton] at hr
      subst r
      exact ⟨by change 0 < 1; decide,trivial⟩
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨trivial,trivial⟩

end PaidSite

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- The actual successor programs of every old or new site have valid box
ordinals and profile widths whenever the inherited programs do. -/
theorem roundSites_schema (ho : ∀ v, (old v).Schema) (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).Schema := by
  change SiteShape e p S at v
  rcases v with oldV | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact (old oldV).schema_retain (ho _) _ _
  · let s := originSite e p bin perm positive first q a siteID edgeID portID
    let x := originWords e (InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID)
    have hr : s.rows = (origin m first).map (RecordCode.read x) := by
      simp [s,originSite,Site.rows,emitted,BankJoint.rows,x]; rfl
    intro r h
    change r ∈ s.rows at h
    rw [hr] at h
    exact ⟨refs_of_empty [] _ (origin_blocks x first []) _ h,origin_read_widthOK m x first r h⟩
  · let s := terminalSite e p bin perm positive first q a siteID edgeID portID binName t
    let x := terminalWords e (InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID) t
    let tail := hookRows e p bin perm positive first q a siteID edgeID portID binName t
    have hr : s.rows = (terminal m).map (RecordCode.read x) ++ tail := by
      simp [s,terminalSite,Site.rows,emitted,BankJoint.rows,x,tail]; rfl
    intro r h
    change r ∈ s.rows at h
    rw [hr,List.mem_append] at h
    rcases h with h | h
    · exact ⟨refs_of_empty [] _ (terminal_blocks x []) _ h,terminal_read_widthOK m x r h⟩
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
      exact ⟨trivial,trivial⟩
  · exact PaidSite.born_schema _ _ _ _ _

end Packing.Inherited

end BorderVNP
end Computability
end OAI
