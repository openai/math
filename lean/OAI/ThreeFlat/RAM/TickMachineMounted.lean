import OAI.ThreeFlat.RAM.TickMachine
import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.RAM.TickFrontMounted
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # The mounted front in the linked physical tick machine -/

noncomputable section
namespace ThreeFlat.RAM.TickMachine

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink DescriptorExpr Diagonal.TickChronology
open Diagonal.ApproximateImage TickActiveROM BitLayout Contraction TickFuel
open scoped Fin.CommRing Classical

attribute [local irreducible] TickPhase.program

theorem mounted_regions (u a teams cap q nt ns np : ℕ) :
    (TickPhysicalABI.mounted u a teams cap q nt ns np).regions = TickIdentity.physicalRegions q nt ns np a := by
  unfold TickPhysicalABI.mounted TickPhysicalABI.layout Layout.regions TickIdentity.physicalRegions
  simp [TickBoundaryFields.base,TickBoundaryFields.Segment.number,BitLayout.hiddenBase]

variable {F : Type*} [Field F] [Fintype F] {p H J w k n m nr mr r : ℕ}
variable {u a teams cap q nt ns np : ℕ}

/-- A single fuel bound for the native front, the identity summand, and a
weighted continuation proved at the physically selected active entry. -/
theorem returns_mounted (field : FieldCode F w) (clock : Clock)
    (fit : Fits (TickWeightedBank.shape F p H J) w)
    (front : TickFrontROM.Reg w k clock ↪ Fin r)
    (registers : Registers (TickPhysicalABI.mounted u a teams cap q nt ns np) clock fit nr mr r k)
    (keys : TickPrefix.Keys k) (data : Fin k → Word w) (evalPublic : Fin 7 → Fin k)
    (nav : Block w n nr k) (prep : Block w m mr k)
    (L : Diagonal.TickAuxiliary.Layout a) (D : Fin q → Bool) (params : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (team step tail : ℕ) (weighted : F)
    (ft : team < 2^nt) (fs : step < 2^ns) (wt : team < 2^w) (ws : step < 2^w)
    (tb : (data keys.teamBase).val = 2+q) (tw : (data keys.teamWidth).val = nt)
    (sb : (data keys.stepBase).val = 2+q+nt) (sw : (data keys.stepWidth).val = ns)
    (hd : clock.groupDuration < 2^w) (hlast : clock.last < 2^w) (wide : 6 < 2^w)
    (room : 2+pinCount q nt ns np a+a < 2^w) :
    let B := TickPhysicalABI.mounted u a teams cap q nt ns np
    let M := program B clock fit front registers keys data evalPublic nav prep
    let ph := clock.phase step
    let enabled := Diagonal.TickAuxiliary.branch L ph oa na
    let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
    let mem := TickMountedPins.memory (w:=w) pins
    ∀ (cfg : Config w (Fintype.card (All (n:=n) (m:=m) (k:=k) B clock fit)) r), cfg.pc = M.entry →
      (∀ f : Config w _ r, enabled = true →
        f.pc = historyLocation B clock fit (.control (.inl (TickFrontROM.phaseNo ph,0))) →
        f.reg (selectedRegs front 0) = (team : Word w) → f.reg (selectedRegs front 1) = (step : Word w) →
        f.reg (selectedRegs front 2) = (ph.tag : Word w) →
        mem (TickControlHeader.markerAddr (w:=w) ph B.oldAux B.newAux).val = 1 →
        Returns field M.program tail f mem weighted) →
      Returns field M.program (159+6*(nt+ns)+25+18*a+tail) cfg mem
        (if enabled then weighted else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0) := by
  dsimp only
  let B := TickPhysicalABI.mounted u a teams cap q nt ns np
  let A := TickIdentity.physicalRegions q nt ns np a
  let ph := clock.phase step
  let enabled := Diagonal.TickAuxiliary.branch L ph oa na
  let mem := TickMountedPins.memory (w:=w) (fields D (digits team nt) (digits step ns) params oa na oc nc)
  let M := program B clock fit front registers keys data evalPublic nav prep
  let R := {registers with control := selectedRegs front}
  let entry := historyEntry (k:=k) (m:=m) (n:=n) B clock fit
  let body := fun j => TickActiveROM.emit B clock fit nav prep (historyLocation B clock fit) R evalPublic
    ((Fintype.equivFin _).symm j)
  have layout : B.regions = A := mounted_regions ..
  have machine_eq : M = TickFrontROM.machine front data keys a A entry body := by
    change TickFrontROM.machine front data keys a B.regions entry body = _
    rw [layout]
  intro cfg start continuation
  have entryPC : cfg.pc = (TickFrontROM.machine front data keys a A entry body).entry := by
    rw [← machine_eq]
    exact start
  obtain ⟨t,ht,f,_,pc,teamVal,stepVal,tag,_,_,sem⟩ := TickFrontROM.run_mounted field clock front data keys L
    entry body D params oa na oc nc team step ft fs wt ws tb tw sb sw hd hlast wide room cfg entryPC
  have tm : f.reg (selectedRegs front 0) = (team : Word w) :=
    Fin.ext (teamVal.trans (Fin.val_cast_of_lt wt).symm)
  have st : f.reg (selectedRegs front 1) = (step : Word w) :=
    Fin.ext (stepVal.trans (Fin.val_cast_of_lt ws).symm)
  have mark : mem (TickControlHeader.markerAddr (w:=w) ph B.oldAux B.newAux).val = TickBitRelation.bitWord w enabled := by
    have eq := TickFrontROM.mounted_marker D params oa na oc nc team step L ph room
    change mem (TickFrontROM.marker (w:=w) A (TickFrontROM.phaseNo ph)).val = _ at eq
    rw [← layout] at eq
    simpa only [TickFrontROM.marker, TickFrontROM.phase_phaseNo, Layout.regions, enabled] using eq
  apply Returns.later (cap:=t+25+18*a+tail) _ (by omega)
  intro extra
  have eq := sem (extra+tail)
  rw [← machine_eq] at eq
  rw [show extra+(t+25+18*a+tail) = extra+tail+25+18*a+t by omega,eq]
  by_cases yes : Diagonal.TickAuxiliary.branch L (clock.phase step) oa na = true
  · have atHead : f.pc = historyLocation (n:=n) (m:=m) (k:=k) B clock fit
        (.control (.inl (TickFrontROM.phaseNo ph,0))) := by
      let addr := TickFrontROM.allPC w k (Fintype.card (Active (n:=n) (m:=m) (k:=k) B clock fit)) clock
      have actual : f.pc = TickFrontROM.historyPC addr (entry (clock.phase step)) := by
        simpa only [ite_eq_left yes] using pc
      exact actual.trans (by rfl)
    have bit : mem (TickControlHeader.markerAddr (w:=w) ph B.oldAux B.newAux).val = 1 := by
      simpa only [enabled, ph, yes, TickBitRelation.bitWord, ite_true] using mark
    have done := continuation f yes atHead tm st tag bit (extra+25+18*a)
    simpa only [ite_eq_left yes,show extra+tail+25+18*a = extra+25+18*a+tail by omega] using done
  · simp only [ite_eq_right yes]


end ThreeFlat.RAM.TickMachine

end
end OAI
