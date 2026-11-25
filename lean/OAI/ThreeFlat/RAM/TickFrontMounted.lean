import OAI.ThreeFlat.RAM.TickFrontRun
import OAI.ThreeFlat.RAM.TickIdentityMounted

namespace OAI
/-! # Both physical marker outcomes on the mounted boundary pins -/

noncomputable section
namespace ThreeFlat.RAM.TickFrontROM

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology Diagonal.ApproximateImage TickBoundaryFields
open scoped Classical Fin.CommRing

attribute [local irreducible] TickPhase.program

variable {w k r n d nt ns np a : ℕ} {F : Type*} [Semiring F]

theorem mounted_marker (D : Fin d → Bool) (params : Fin np → Bool) (oa na oc nc : Fin a → Bool)
    (team step : ℕ) (L : Diagonal.TickAuxiliary.Layout a) (ph : Phase)
    (room : 2+pinCount d nt ns np a+a < 2^w) :
    let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
    TickMountedPins.memory (w:=w) pins (marker (w:=w) (TickIdentity.physicalRegions d nt ns np a) (phaseNo ph)).val =
      TickBitRelation.bitWord w (Diagonal.TickAuxiliary.branch L ph oa na) := by
  let i : Fin a := ⟨0,L.marker.trans_le (L.ordered.trans L.fits)⟩
  let loc := TickMountedPins.has_fields (w:=w) (nt:=nt) (ns:=ns) D params oa na oc nc team step
  have fit := TickIdentity.physicalFits room
  have old := boundary_bit .oldAux i loc (le_refl _)
  have new := boundary_bit .newAux i loc (le_refl _)
  have bo : base 2 d nt ns np a .oldAux < 2^w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) fit.oldAux
  have bn : base 2 d nt ns np a .newAux < 2^w :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) fit.newAux
  by_cases p : ph = .opening
  · simpa only [marker,phase_phaseNo,TickControlHeader.markerAddr,TickIdentity.physicalRegions,
      Diagonal.TickAuxiliary.branch,ite_eq_left p,Fin.val_cast_of_lt bn,Segment.select,
      i,Nat.add_zero,TickMountedPins.memory] using new
  · simpa only [marker,phase_phaseNo,TickControlHeader.markerAddr,TickIdentity.physicalRegions,
      Diagonal.TickAuxiliary.branch,ite_eq_right p,Fin.val_cast_of_lt bo,Segment.select,
      i,Nat.add_zero,TickMountedPins.memory] using old

/-- On the mounted tensor input, the opening reads the new auxiliary marker
and the other phases read the old marker. The zero summand evaluates the
actual auxiliary-zero and chunk-equality indicator. -/
theorem run_mounted (field : FieldCode F w) (clock : Clock) (reg : Reg w k clock ↪ Fin r)
    (data : Fin k → Word w) (keys : TickPrefix.Keys k) (L : Diagonal.TickAuxiliary.Layout a)
    (hEntry : Phase → Fin n) (hist : Fin n → Instr w (Fintype.card (Labels w k n clock)) r k)
    (D : Fin d → Bool) (params : Fin np → Bool) (oa na oc nc : Fin a → Bool) (teamID stepID : ℕ)
    (ft : teamID < 2^nt) (fs : stepID < 2^ns) (wt : teamID < 2^w) (ws : stepID < 2^w)
    (tb : (data keys.teamBase).val = 2+d) (tw : (data keys.teamWidth).val = nt)
    (sb : (data keys.stepBase).val = 2+d+nt) (sw : (data keys.stepWidth).val = ns)
    (hd : clock.groupDuration < 2^w) (hlast : clock.last < 2^w) (wide : 6 < 2^w)
    (room : 2+pinCount d nt ns np a+a < 2^w)
    (cfg : Config w (Fintype.card (Labels w k n clock)) r)
    (start : cfg.pc = (machine reg data keys a (TickIdentity.physicalRegions d nt ns np a) hEntry hist).entry) :
    let A := TickIdentity.physicalRegions d nt ns np a
    let M := machine reg data keys a A hEntry hist
    let pins := fields D (digits teamID nt) (digits stepID ns) params oa na oc nc
    let mem := TickMountedPins.memory (w:=w) pins
    let loc := allPC w k n clock
    let R := prefixReg reg
    let ph := clock.phase stepID
    let enabled := Diagonal.TickAuxiliary.branch L ph oa na
    ∃ t ≤ 159+6*(nt+ns), ∃ f, advance M.program t cfg mem = some (f,mem) ∧
      f.pc = (if enabled then historyPC loc (hEntry ph) else idPC loc (TickIdentity.block w a A).first) ∧
      (f.reg (TickPrefix.team R 2)).val = teamID ∧ (f.reg (TickPrefix.step R 2)).val = stepID ∧
      f.reg (TickPrefix.tag R) = (ph.tag : Word w) ∧ f.persistent = cfg.persistent ∧
      f.privateMem = cfg.privateMem ∧ ∀ fuel, mass field M.program (fuel+25+18*a+t) cfg mem =
        if enabled then mass field M.program (fuel+25+18*a) f mem
        else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0 := by
  let A := TickIdentity.physicalRegions d nt ns np a
  let pins := fields D (digits teamID nt) (digits stepID ns) params oa na oc nc
  let mem := TickMountedPins.memory (w:=w) pins
  let ph := clock.phase stepID
  let bit := Diagonal.TickAuxiliary.branch L ph oa na
  have addr : 2+d+nt+ns < 2^w := by unfold pinCount at room; omega
  have loc := TickMountedPins.has_fields (w:=w) (nt:=nt) (ns:=ns) D params oa na oc nc teamID stepID
  have marker' : mem (marker (w:=w) A (phaseNo ph)).val = TickBitRelation.bitWord w bit :=
    mounted_marker D params oa na oc nc teamID stepID L ph room
  have valid : TickIdentity.valid A mem a ↔ _ := TickIdentity.valid_mounted D params oa na oc nc teamID stepID room
  have nz : (1 : Word w) ≠ 0 := by
    intro h
    have x := congrArg Fin.val h
    rw [show (1 : Word w).val = 1 from Fin.val_cast_of_lt (by omega : 1 < 2^w)] at x
    exact Nat.one_ne_zero x
  obtain ⟨t,ht,f,adv,pc,team,step,tag,per,priv,sem⟩ := run field clock reg data keys A hEntry hist
    D params oa na oc nc teamID stepID 2 (2+pinCount d nt ns np a) (TickMountedPins.word pins)
    loc le_rfl addr ft fs wt ws tb tw sb sw hd hlast wide (TickIdentity.physicalFits room)
    (fun j => TickMountedPins.memory_hidden pins j.val) cfg start
  let yesPC := historyPC (allPC w k n clock) (hEntry ph)
  let noPC := idPC (allPC w k n clock) (TickIdentity.block w a A).first
  let program := (machine reg data keys a A hEntry hist).program
  refine ⟨t,ht,f,adv,?_,team,step,tag,per,priv,?_⟩
  · change f.pc = (if mem (marker (w:=w) A (phaseNo ph)).val = 0 then noPC else yesPC) at pc
    change f.pc = (if bit then yesPC else noPC)
    rw [marker'] at pc
    cases h : bit <;> simpa [h, TickBitRelation.bitWord, nz] using pc
  · intro fuel
    have result : mass field program (fuel+25+18*a+t) cfg mem =
        if mem (marker (w:=w) A (phaseNo ph)).val = 0 then
          (if TickIdentity.valid A mem a then 1 else 0)
        else mass field program (fuel+25+18*a) f mem := sem fuel
    change mass field program (fuel+25+18*a+t) cfg mem =
      if bit then mass field program (fuel+25+18*a) f mem
      else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0
    rw [marker'] at result
    cases h : bit <;> simpa [h, TickBitRelation.bitWord, nz, valid] using result


end ThreeFlat.RAM.TickFrontROM

end
end OAI
