import OAI.Computability.VPVNP.CompressorRecordRefreshDeterminism

/-!
# Intermediate source records of a native degree refresh

A complete native trace is split just before and just after the selected term pass.
The stored demand values, external segments and selected supply records are identified
in those same memories by determinism. The four output scans likewise use the
actual selected source tables and completed incidence columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Build

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open NewSlots RefreshRAM Allocation
open private bounds demand_bound from OAI.Computability.VPVNP.CompressorRecordRefreshBuild

variable {w a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (c : DyadicRefreshChoice X E hdH conn F)
  (ties : Fin t ≃ Tie (2^a)) (T : IncidenceDirectory w) (start stride : ℕ)
local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P w
local notation "D" => word (bits := w) (Plan.demand P)
local notation "M" => word (bits := w) (Plan.term P)
local notation "V" => dyadicRefreshNext X E hdH conn F hD hd c
local notation "Fₛ" => blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)

/-- The old represented graph and the admitted branch establish both sources
needed by the deterministic post-term stages. -/
theorem middle_records (L : PrepareLayout X T a₀ dH t stride start) (initial m₁ : Memory w)
    (old : T.Represents X initial) (pre tr : List (Report w))
    (prep : PrepareRun X T Q D ties (word (2^g)) L.regions.fits initial m₁ pre)
    (wide : 2+2^a*dH ≤ stride) (room : (P).stop < 2^w)
    (termBits : termConstant E hdH conn F ties + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (nextWidth : (V).maxWireWidth < 2^w) (cap : ℕ) (capFit : TermWorker.budget F t (2^a*dH) w X.maxWireWidth ≤ cap)
    (native : termRun E hdH conn F ties X D M stride cap (blockTapes E hdH conn F X c w) m₁ = some tr) :
    (∀ s, DemandPreparation.demandAt ties (DemandScan.rowBase X t D s) m₁ = Fₛ s) ∧
      SegmentFields X Q L.regions.fits (after m₁ (eventLog tr)) ∧
      SupplyScan.TermFields X E hdH conn F c M stride (after m₁ (eventLog tr)) := by
  have external := (bounds X E hdH conn F hD hd c nextWidth).1
  obtain ⟨p,m',hp,seg,dem,_,_⟩ := prepare_demands X T Q D ties initial old (word (2^g)) L.degree L.lanes
    L.regions L.directory L.gather L.baseApart external L.demandRoom L.demandApart
  have hm := (PrepareRun.deterministic hp prep).2
  subst m'
  obtain ⟨terms,rt,termFields,_,frame,_,_⟩ := term_pass E hdH conn F ties X D M stride wide L.demandTerm
    L.termRoom m₁ X.maxWireWidth termBits (demand_bound X) dem cap capFit c
  obtain rfl := Option.some.inj (rt.symm.trans native)
  have td : (P).demand ≤ (P).term := Nat.le_add_right ..
  have ts : (P).term ≤ (P).stop := by dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort,Plan.supply]; omega
  have wordTerm : (M).val = (P).term := Nat.mod_eq_of_lt (ts.trans_lt room)
  refine ⟨dem,seg.transfer X Q (fun j hj i hi ↦ ?_),termFields⟩
  apply frame
  apply Or.inl
  rw [wordTerm]
  exact ((P).scratch_interval (td.trans (ts.trans room.le)) j hj i hi).2.trans_le td

/-- The post-term scans consume the precise initialized tables. Their old and
new source memories are the actual prefix memories of the reported execution. -/
theorem output_records (m : Memory w) (ss es os : List (Report w)) (wide : 2+2^a*dH ≤ stride)
    (room : (P).stop < 2^w) (nextWidth : (V).maxWireWidth < 2^w) (fit : (P).segments ≤ 2^w)
    (segments : SegmentFields X Q fit m) (terms : SupplyScan.TermFields X E hdH conn F c M stride m)
    (srun : let b := SupplyScan.params (2^a) (2^g) dH M stride F.selectorBits ((P).inputs w).supply
      runSegment ((template SupplyScan.visit 0).instantiate w b).program 34 (some 0) m
        (List.replicate ((P).sites*dH) []) = some ss)
    (erun : ExpanderROM.runRows E ((P).inputs w) (some 0) (after m (eventLog ss)) (List.finRange (2^a*dH)) = some es)
    (orun : let kinds := fun j : Fin (2^a₀) ↦ kindOf ((refreshSlots hd).symm j)
      let data := fun j : Fin (2^a₀) ↦ AllSlots.words (2^a) (2^g) ((P).inputs w) ((P).output w) ((refreshSlots hd).symm j)
      AllSlots.Runs kinds data (P).sites (List.finRange (2^a₀)) (after (after m (eventLog ss)) (eventLog es)) os) :
    let m₂ := after (after m (eventLog ss)) (eventLog es)
    AllSlots.SourceTables X E hdH conn F c ((P).inputs w) m₂ ∧ ((P).output w).ActualColumns V (after m₂ (eventLog os)) := by
  intro m₂
  have layout := finish_layout X E hdH conn F hD hd c t stride start wide room.le
  have internal := (bounds X E hdH conn F hD hd c nextWidth).2
  obtain ⟨ss',es',hs,he,src,_,_,_⟩ := Finish.supply_and_rom X E hdH conn F hD hd c Q M stride
    ((P).inputs w) ((P).output w) m fit segments terms layout internal
  obtain rfl := Option.some.inj (hs.symm.trans srun)
  obtain rfl := Option.some.inj (he.symm.trans erun)
  obtain ⟨os',ro,actual,_,_⟩ := AllSlots.all_slots X E hdH conn F hD hd c ((P).inputs w) ((P).output w) m₂
    src layout.dims layout.incidence layout.slotReads
  obtain rfl := AllSlots.Runs.deterministic ro orun
  exact ⟨src,actual⟩

end CompressorRecords.PortRefresh.Build

end VPVNP
end Computability
end OAI
