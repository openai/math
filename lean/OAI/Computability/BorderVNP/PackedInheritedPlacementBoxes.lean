import OAI.Computability.BorderVNP.PackedInheritedPlacement
import OAI.Computability.BorderVNP.PackedBankRoundSchema
import OAI.Computability.BorderVNP.PackedBottomGridSite

/-! # Relative one-copy factors in all physically generated site programs

Bottom staging replaces weighted unary tests by relative truth tables and
explicit incidence checks. Paid births use a gadget table, and selector
births have an empty one-copy list. Retention adds only compressed equalities.
These constructors justify leaving all private table bytes in place when
the actual site programs are relocated into the merged cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse Crossing Shortening Shortening.StaticRows Shortening.CombiningStep

/-- Every table in this persistent site uses only factor-relative addresses. -/
def Site.RelativeBoxes (s : Site) : Prop :=
  ∀ fs ∈ s.boxes, ∀ f ∈ fs, ∀ off, f.shift off = f

/-- Relative stored factors supply the relocation law for every visited copy and local entry. -/
theorem Site.RelativeBoxes.reachable {s : Site} (h : s.RelativeBoxes) (off : ℕ) :
    ∀ o ∈ s.directory.occurrences, o.factor.shift off = o.factor := by
  intro o ho
  obtain ⟨r,_,hread⟩ := List.mem_flatMap.mp ho
  cases r with
  | box id base copies stride =>
    change o ∈ (List.range copies).flatMap (fun i => (s.boxes.getD id []).map
      (fun f => (⟨f,base+i*stride,i⟩ : Occurrence))) at hread
    obtain ⟨_,_,hin⟩ := List.mem_flatMap.mp hread
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hin
    by_cases hi : id < s.boxes.length
    · rw [List.getD_eq_getElem s.boxes [] hi] at hf
      exact h _ (List.getElem_mem hi) f hf off
    · rw [List.getD_eq_default s.boxes [] (Nat.le_of_not_gt hi)] at hf
      cases hf
  | _ => cases hread

/-- Moving an existing site through another cut layer reuses its original relative factors. -/
theorem Site.RelativeBoxes.retain {s : Site} (h : s.RelativeBoxes) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).RelativeBoxes := h

/-- The sparse birth constructors preserve the relative-address property across each selected round. -/
theorem roundSites_relative {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool)
    (first : Fin D × Bool) (q : Counts e p bin perm) (binName : S → ℕ) (position : e.Entry → ℕ)
    {ns ne np : ℕ} (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice) (rel : ∀ v, (old v).RelativeBoxes)
    (v : (output e p bin perm positive first q).layout.Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).RelativeBoxes := by
  change SiteShape e p S at v
  rcases v with v|⟨a,(_|t|⟨i,v⟩)⟩
  · exact rel v
  · intro fs hf; cases hf
  · intro fs hf; cases hf
  · intro fs hf f hmem off
    change fs ∈ [[PaidBox.tableFactor e position i v]] at hf
    obtain rfl := List.mem_singleton.mp hf
    obtain rfl := List.mem_singleton.mp hmem
    rfl

end Packing.Inherited

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes Inherited
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

/-- Every bottom birth uses only relative factor tables after staging all weighted sources. -/
theorem born_relative (copies capFine capReport : ℕ) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).RelativeBoxes := by
  intro fs hfs f hf off
  obtain rfl := List.mem_singleton.mp hfs
  exact stored_shift N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
    rules capFine capReport off f hf

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
