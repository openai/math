import OAI.Computability.BorderVNP.PackedBankRoundSchema
import OAI.Computability.BorderVNP.PackedBankProfileRowSize

/-! # Scalar field count of every stored row throughout a crossing round

Retained cuts add equalities. The new profile sites draw their rows from the
fixed alphabet of the paid crossing identity, and the paid boxes add only
equalities and a box reference. A single row bound thus propagates through
all selected rounds without a factor depending on the number of rounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Rebasing the stored ordinal of a paid box preserves its number of fields. -/
@[simp] theorem Record.packet_length_rebaseBox (r : Record) (base : ℕ) :
    (Packet.record (r.rebaseBox base)).length = (Packet.record r).length := by cases r <;> rfl

end CellSparse

namespace Packing.Inherited

open CellSparse Crossing Shortening Shortening.CombiningStep Shortening.StaticRows
  BankPacket BankJoint InheritedProfile
open scoped Classical

/-- Bound on the number of fields passed to the individual public row printer. -/
def Site.RowBound (s : Site) (R : ℕ) : Prop := ∀ r ∈ s.rows, (Packet.record r).length ≤ R

/-- A retained site adds one nine-field equality per translated interval. -/
theorem Site.rowBound_retain (s : Site) {R : ℕ} (h : s.RowBound R) (hR : 9 ≤ R)
    (n : ℕ) (cuts : List Slice) : (s.retain n cuts).RowBound R := by
  intro r hr
  rw [s.retain_rows,List.mem_append] at hr
  rcases hr with hr | hr
  · exact h r hr
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hr
    exact hR

/-- The absolute placement preserves the same per-row bound in the merged packet. -/
theorem Site.rowBound_placed (s : Site) {R : ℕ} (h : s.RowBound R) (off base : ℕ) :
    ∀ r ∈ s.placedRows off base, (Packet.record r).length ≤ R := by
  intro r hr
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  simpa only [Record.packet_length_rebaseBox,Record.packet_length_shift] using h t ht

namespace PaidSite

/-- Every field list in a newly installed paid box is an equality or a single box reference. -/
theorem born_rowBound {n : ℕ} (w : Fin n → ℕ) (c input : ℕ) (starts : Fin n → ℕ) (f : Factor) :
    (born w c input starts f).RowBound 9 := by
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
      exact Nat.le_refl 9
    · simp only [List.map_cons,List.map_nil,List.mem_singleton] at hr
      subst r
      exact (by decide : 5 ≤ 9)
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact Nat.le_refl 9

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

/-- A fixed coefficient chosen from the paid alphabet and initial grid rows
also bounds every actual row at every successor site. -/
theorem roundSites_rowBound {R : ℕ} (hR : 16*(e.count+1) ≤ R) (ho : ∀ v, (old v).RowBound R)
    (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).RowBound R := by
  have h9 : 9 ≤ R := by omega
  change SiteShape e p S at v
  rcases v with oldV | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact (old oldV).rowBound_retain (ho _) h9 _ _
  · let s := originSite e p bin perm positive first q a siteID edgeID portID
    let x := originWords e (InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID)
    have hr : s.rows = (origin m first).map (RecordCode.read x) := by
      simp [s,originSite,Site.rows,emitted,BankJoint.rows,x]; rfl
    intro r h
    change r ∈ s.rows at h
    rw [hr] at h
    exact (origin_read_row_size m x first r h).trans hR
  · let s := terminalSite e p bin perm positive first q a siteID edgeID portID binName t
    let x := terminalWords e (InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID) t
    let tail := hookRows e p bin perm positive first q a siteID edgeID portID binName t
    have hr : s.rows = (terminal m).map (RecordCode.read x) ++ tail := by
      simp [s,terminalSite,Site.rows,emitted,BankJoint.rows,x,tail]; rfl
    intro r h
    change r ∈ s.rows at h
    rw [hr,List.mem_append] at h
    rcases h with h | h
    · exact (terminal_read_row_size m x r h).trans hR
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
      exact h9
  · intro r hr
    exact (PaidSite.born_rowBound _ _ _ _ _ r hr).trans h9

end Packing.Inherited

end BorderVNP
end Computability
end OAI
