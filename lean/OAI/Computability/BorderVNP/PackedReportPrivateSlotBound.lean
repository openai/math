import OAI.Computability.BorderVNP.PackedNativeDemandPlacement
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsPlacement
import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.FiniteEvaluatorCellKey

/-! # The actual allocated interval of every original signed report descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses Directory Directory.PrivateBank RoutingISA
open private prefix_le from OAI.Computability.BorderVNP.PackedRoutingPrefix
open scoped Classical

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)

/-- An actual original description occupies a subinterval of its receiving
cell's private descriptor store, after both the supplied inputs and report gap. -/
theorem private_description_interval (j : Fin dir.entries) :
    let c := cell (old j)
    let offset := (destination N cell edge port dir old live gap (.inl j)).2
    suppliedSize N cell c+gap ≤ offset ∧ offset+dir.description ≤ suppliedSize N cell c+gap+dir.entries*dir.description := by
  intro c offset
  let sc := Sum.elim (fun x : SuppliedWord N cell => x.1) (id : Fin C → Fin C)
  let sizes := Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)
  let key := reserveID (C:=C) (suppliedID N cell edge port)
  let byRow (i : ℕ) := if h : i<dir.entries then (cell (old ⟨i,h⟩)).val else 0
  have decode (i : Fin dir.entries) : byRow i.val=(cell (old i)).val := dite_eq_left i.isLt
  have eq : offset=DataSlabs.size sc sizes c+PrivatePlacement.prefixCounts byRow dir.description j.val c.val :=
    base_private sc (cell ∘ old) key sizes dir.description byRow decode j
  have volume : DataSlabs.size sc sizes c=suppliedSize N cell c+gap := by
    rw [show DataSlabs.size sc sizes c=_ from reservedSize (fun x : SuppliedWord N cell => x.1) (supplyWidth N cell) gap c,
      dataSlabs_size]
  have prefixBound := prefix_le byRow dir.description j.val c.val
  have endBound := Nat.mul_le_mul_right dir.description (show j.val+1≤dir.entries from j.isLt)
  rw [Nat.add_mul,Nat.one_mul] at endBound
  omega

end Packing.RoutingOutputs.NativeDemands

namespace DiagonalTallyCellReports.ReportDirectory

open Crossing Packing Packing.CellAddresses Packing.BundleDirectory RoutingISA
open Packing.RoutingOutputs.NativeDemands
open scoped Classical

/-- All compact rows of an actual routed source have disjoint report and
descriptor regions once the report tail and per-cell volume fit the native
arena. The private header address is the one from the typed native demand. -/
theorem source_description_intervals {D C ns np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ns) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap start stride : ℕ) (l : ReportLayout) (src : Fin dir.entries → ReportBundle)
    (state : N.Site → Packing.Inherited.Site) (team : ℕ) (who size : ℕ → ℕ) (digits : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)
    (slots : ∀ j, (src j).header.siteSlot=start+(cell (old j)).val*stride+
      (destination N cell edge port dir old live gap (.inl j)).2)
    (strideBound : ∀ c : Fin C, suppliedSize N cell c+gap+dir.entries*dir.description ≤ stride) :
    let key := fun v => (cell v).val
    let rows := sourceCells l (cell ∘ old) src team who (fun c => start+c*stride) (fun n => suppliedSize N key n) size digits
    (∀ c∈rows,c.tailWidth≤gap) → SiteIntervals rows dir.description stride := by
  intro key rows tail c hc b hb
  have mem := hc
  change c ∈ ((List.range C).filter _).map _ at mem
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
  change b ∈ (sourceRows (cell ∘ old) i).map src at hb
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
  have eq : (cell (old j)).val=i := mem_sourceRows.mp hj
  let home := cell (old j)
  have keyWidth : suppliedSize N key i=suppliedSize N cell home := by
    rw [←eq]
    exact (FiniteEvaluator.Merged.CellKey.bankSizes N cell Fin.valEmbedding home state).2.2
  have within := private_description_interval N cell edge port dir old live gap j
  have reportGap := tail _ hc
  have storage := strideBound home
  change start+i*stride+suppliedSize N key i+_≤(src j).header.siteSlot ∧
    (src j).header.siteSlot+dir.description ≤ start+i*stride+stride
  rw [slots,eq,keyWidth]
  dsimp only [home] at storage ⊢
  omega

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
