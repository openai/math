import OAI.Computability.BorderVNP.CellPacketInputSize

/-! # Quantitative assembly of the site descriptions in a cell packet

The sorted site order fixes the order of the box tables. Public box references are
cell-local ordinals in this merged order. Reported count words are supplied once for
the whole cell. Static factor costs use the table selected by each actual reference.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

variable {ι : Type*}

/-- Combine the ordered site table fragments and wiring fragments into the input of one
cell. The public rows contain the final ordinals of their private box tables. -/
def Directory.mergeSites (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) : Directory :=
  ⟨sites.flatMap tables,sites.flatMap rows,reports⟩

namespace Directory

/-- Nodes in the public wiring fragments before adding the final terminator. -/
def recordNodes (rs : List Record) := rs.length + (rs.map Record.guardMassBound).sum

/-- Nodes in the one-copy factor sweeps before adding their final terminator. -/
def blockNodes (bs : List BoxBlock) :=
  (bs.map fun b => 4+b.factors.length+(b.factors.map fun f => 10000*f.staticMass).sum).sum

/-- Private table mass includes every stored box, even a table with no references. -/
def tableNodes (bs : List (List Factor)) :=
  bs.length + (bs.map fun fs => (fs.map Factor.staticMass).sum).sum

/-- Resolve the site rows against the actual final table ordering. -/
def resolvedRows (tables : List (List Factor)) (rs : List Record) : List BoxBlock :=
  (⟨tables,rs,[]⟩ : Directory).blocks

/-- Exact public row order of all references to the merged box table. -/
theorem mergeSites_blocks (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    (mergeSites sites tables rows reports).blocks =
      sites.flatMap (fun i => resolvedRows (sites.flatMap tables) (rows i)) := List.filterMap_flatMap

private theorem sum_flat {α β : Type*} (is : List α) (a : α → List β) (f : β → ℕ) :
    ((is.flatMap a).map f).sum = (is.map fun i => ((a i).map f).sum).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [ih]

private theorem nodes_flat {α β : Type*} (is : List α) (a : α → List β) (f : β → ℕ) :
    (is.flatMap a).length+((is.flatMap a).map f).sum =
      (is.map fun i => (a i).length+((a i).map f).sum).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    omega

/-- Public syntax sums the actual row charges of the retained and new sites. -/
theorem mergeSites_recordMass (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    (mergeSites sites tables rows reports).recordMass =
      (sites.map fun i => recordNodes (rows i)).sum+1 := by
  unfold mergeSites recordMass recordNodes
  rw [nodes_flat]

/-- Static sweep charge for the cell, with each referenced one-copy table resolved in place. -/
theorem mergeSites_boxMass (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    (mergeSites sites tables rows reports).boxMass =
      (sites.map fun i => blockNodes (resolvedRows (sites.flatMap tables) (rows i))).sum+1 := by
  rw [boxMass,sweepMass,mergeSites_blocks,sum_flat]
  rfl

/-- Total expanded number of visited factors in all actually referenced boxes. -/
theorem mergeSites_visitCount (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    (mergeSites sites tables rows reports).visitCount =
      (sites.map fun i => ((resolvedRows (sites.flatMap tables) (rows i)).map
        fun b => b.copies*b.factors.length).sum).sum := by
  rw [visitCount,mergeSites_blocks,sum_flat]

/-- Original private input storage is additive across the site fragments. -/
theorem mergeSites_storedMass (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) :
    Packet.storedMass (mergeSites sites tables rows reports) =
      (sites.map fun i => tableNodes (tables i)).sum := nodes_flat sites tables _

/-- Sufficient per-site sums for the static description bound. Gadget reports remain one
cell-wide list and introduce no multiplicity depending on the number of sites. -/
theorem mergeSites_static (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) {A M : ℕ}
    (hr : (sites.map fun i => recordNodes (rows i)).sum+1 ≤ A*(M+1)^2)
    (hb : (sites.map fun i => blockNodes (resolvedRows (sites.flatMap tables) (rows i))).sum+1 ≤ A*(M+1))
    (hd : (reports.map List.length).sum ≤ A*(M+1)^2) (hc : reports.length ≤ A*(M+1)) :
    (mergeSites sites tables rows reports).StaticBounds A M := by
  refine ⟨?_,?_,hd,hc⟩
  · rw [mergeSites_recordMass]; exact hr
  · rw [mergeSites_boxMass]; exact hb

/-- Every original scalar field belongs to one of the specified site slices or to a
single cell-wide report word. This includes the length prefixes of the three lists. -/
theorem mergeSites_raw (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) {U p : ℕ} (hp : p ≤ U)
    (ht : (sites.map fun i => (tables i).length).sum ≤ U)
    (hr : (sites.map fun i => (rows i).length).sum ≤ U) (hc : reports.length ≤ U)
    (hboxes : ∀ i ∈ sites, ∀ fs ∈ tables i, fs.length ≤ U ∧ ∀ f ∈ fs, Packet.FactorFields f U)
    (hrows : ∀ i ∈ sites, ∀ r ∈ rows i, Packet.RecordFields r U)
    (hreports : ∀ bs ∈ reports, bs.length ≤ U ∧ ∀ a ∈ bs, a ≤ U) :
    Packet.RawFields (mergeSites sites tables rows reports) p U := by
  refine ⟨hp,⟨?_,?_,hc⟩,?_,?_,hreports⟩
  · exact (List.length_flatMap ..).le.trans ht
  · exact (List.length_flatMap ..).le.trans hr
  · intro fs hfs
    obtain ⟨i,hi,hb⟩ := List.mem_flatMap.mp hfs
    exact hboxes _ hi _ hb
  · intro r hrr
    obtain ⟨i,hi,hb⟩ := List.mem_flatMap.mp hrr
    exact hrows _ hi _ hb

/-- Generator fields can use the smaller local numeric limit even when the original
packet contains global identifiers with larger magnitude. Only the chosen box table
and its local addressing fields enter each generated block. -/
theorem mergeSites_compact (sites : List ι) (tables : ι → List (List Factor))
    (rows : ι → List Record) (reports : List (List ℕ)) {U p : ℕ} (hp : p ≤ U)
    (hv : (sites.map fun i => ((resolvedRows (sites.flatMap tables) (rows i)).map
      fun b => b.copies*b.factors.length).sum).sum ≤ U)
    (hw : ∀ i ∈ sites, ∀ r ∈ rows i, r.GuardBound U)
    (hb : ∀ i ∈ sites, ∀ b ∈ resolvedRows (sites.flatMap tables) (rows i),
      b.HeaderBound U ∧ ∀ f ∈ b.factors, f.FieldBound U)
    (hr : ∀ bs ∈ reports, bs.length ≤ U ∧ ∀ v ∈ bs, v ≤ U) :
    (mergeSites sites tables rows reports).CompactFields p U := by
  refine ⟨hp,(mergeSites_visitCount ..).le.trans hv,?_,?_,hr⟩
  · intro r hrs
    obtain ⟨i,hi,hri⟩ := List.mem_flatMap.mp hrs
    exact hw _ hi _ hri
  · intro b hbs
    rw [mergeSites_blocks] at hbs
    obtain ⟨i,hi,hbi⟩ := List.mem_flatMap.mp hbs
    exact hb _ hi _ hbi

end Directory

/-- A local field bound suffices for the generator even when its factors use
much larger global gadget IDs. -/
theorem Directory.compact_of_local {D : Directory} {p V : ℕ} (hp : p ≤ V) (hv : D.visitCount ≤ V)
    (hrows : ∀ r ∈ D.records, Packet.RecordFields r V)
    (hboxes : ∀ fs ∈ D.boxes, fs.length ≤ V ∧ ∀ f ∈ fs, f.FieldBound V)
    (hrep : ∀ bs ∈ D.reportedCounts, bs.length ≤ V ∧ ∀ x ∈ bs, x ≤ V) :
    D.CompactFields p V := by
  refine ⟨hp,hv,fun r hr => (hrows r hr).1,?_,hrep⟩
  intro b hb
  obtain ⟨r,hr,e⟩ := List.mem_filterMap.mp hb
  cases r with
  | zero | equal | profile => cases e
  | box id base copies stride =>
    change some ⟨base,copies,stride,D.boxes.getD id []⟩ = some b at e
    cases e
    obtain ⟨_,_,hbase,hc,hs⟩ := hrows (.box id base copies stride) hr
    by_cases hi : id < D.boxes.length
    · rw [List.getD_eq_getElem _ _ hi]
      have hb := hboxes _ (List.getElem_mem hi)
      exact ⟨⟨hbase,hs,hc,hb.1⟩,hb.2⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
      exact ⟨⟨hbase,hs,hc,Nat.zero_le _⟩,by simp⟩

/-- Reading a directory whose source fields are bounded also bounds every generated
header. Missing box identifiers resolve to the empty list by the original directory
semantics. The expanded visit count is charged separately. -/
theorem Packet.RawFields.compact {D : Directory} {p U : ℕ} (h : Packet.RawFields D p U)
    (visits : D.visitCount ≤ U) : D.CompactFields p U :=
  D.compact_of_local h.privateWires visits h.records
    (fun fs hfs => ⟨(h.boxes fs hfs).1, fun f hf => ((h.boxes fs hfs).2 f hf).1⟩) h.reports

end CellSparse

end BorderVNP
end Computability
end OAI
