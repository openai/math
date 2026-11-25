import OAI.ThreeFlat.RAM.TickFrontROM

namespace OAI
/-! # Execution of the closed native tick front and its weighted identity branch -/

noncomputable section
namespace ThreeFlat.RAM.TickFrontROM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Diagonal.TickChronology Diagonal.ApproximateImage
open scoped Classical Fin.CommRing

attribute [local irreducible] TickPhase.program

variable {w k r n : ℕ} {F : Type*} [Semiring F]

/-- The machine reads both physical identifiers and the phase-selected marker
before entering its branch. A zero marker computes the closed identity
indicator, while a nonzero marker enters the supplied history text with
all three decoded control words available in their original registers. -/
theorem run (field : FieldCode F w) (clock : Clock) (reg : Reg w k clock ↪ Fin r)
    (data : Fin k → Word w) (keys : TickPrefix.Keys k)
    {d nt ns np a : ℕ} (regions : TickIdentity.Regions) (hEntry : Phase → Fin n)
    (hist : Fin n → Instr w (Fintype.card (Labels w k n clock)) r k)
    (D : Fin d → Bool) (params : Fin np → Bool) (oldA newA oldC newC : Fin a → Bool)
    (teamID stepID off S : ℕ) (hdr : ℕ → Word w)
    (layout : TickReadFields.HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC teamID stepID hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (addr : off+d+nt+ns < 2^w)
    (ft : teamID < 2^nt) (fs : stepID < 2^ns) (wt : teamID < 2^w) (ws : stepID < 2^w)
    (tb : (data keys.teamBase).val = off+d) (tw : (data keys.teamWidth).val = nt)
    (sb : (data keys.stepBase).val = off+d+nt) (sw : (data keys.stepWidth).val = ns)
    (hd : clock.groupDuration < 2^w) (hlast : clock.last < 2^w) (wide : 6 < 2^w)
    (fit : regions.Fits w a) (zero : ∀ j : Fin a, initialMemory S hdr (regions.zero+j.val) = 0)
    (cfg : Config w (Fintype.card (Labels w k n clock)) r)
    (start : cfg.pc = (machine reg data keys a regions hEntry hist).entry) :
    let M := machine reg data keys a regions hEntry hist
    let mem := initialMemory S hdr
    let L := allPC w k n clock
    let R := prefixReg reg
    let ph := clock.phase stepID
    let bit := mem (marker (w:=w) regions (phaseNo ph)).val
    ∃ t ≤ 159+6*(nt+ns), ∃ f, advance M.program t cfg mem = some (f,mem) ∧
      f.pc = (if bit=0 then idPC L (TickIdentity.block w a regions).first else historyPC L (hEntry ph)) ∧
      (f.reg (TickPrefix.team R 2)).val = teamID ∧ (f.reg (TickPrefix.step R 2)).val = stepID ∧
      f.reg (TickPrefix.tag R) = (ph.tag : Word w) ∧ f.persistent = cfg.persistent ∧
      f.privateMem = cfg.privateMem ∧ ∀ fuel, mass field M.program (fuel+25+18*a+t) cfg mem =
        if bit=0 then (if TickIdentity.valid regions mem a then 1 else 0)
        else mass field M.program (fuel+25+18*a) f mem := by
  let M := machine reg data keys a regions hEntry hist
  let mem := initialMemory S hdr
  let L := allPC w k n clock
  let R := prefixReg reg
  let ph := clock.phase stepID
  let z := marker (w:=w) regions (phaseNo ph)
  let exit := idPC L (TickIdentity.block w a regions).first
  have rom := installed reg data keys a regions hEntry hist
  obtain ⟨t,ht,b,read,bpc,bTeam,bStep,bTag,bPer,bPriv⟩ := TickPrefix.advance_emit M clock
    (prefixPC L) R keys (fun q => switchPC L (phaseNo q) 0) (fun j => rom (.inl j))
    D params oldA newA oldC newC teamID stepID off S hdr layout bound addr ft fs wt ws
    tb tw sb sw hd hlast wide cfg start
  have switchROM (i : Fin 4) : M.code (switchPC L (phaseNo ph) i) =
      TickMarkerSwitch.emit (switchPC L (phaseNo ph)) (switchReg reg) z exit (historyPC L (hEntry ph)) i := by
    simpa only [M, L, z, exit, switchPC, emit, phase_phaseNo] using rom (.inr (.inl (phaseNo ph,i)))
  obtain ⟨f,fpc,keep,fp,fm,choice⟩ := TickMarkerSwitch.advance_switch M (switchPC L (phaseNo ph))
    (switchReg reg) z exit (historyPC L (hEntry ph)) switchROM b mem bpc
  have saved (i : TickPrefix.Slots w k clock) : f.reg (R i) = b.reg (R i) := by
    apply keep
    intro j
    exact reg.injective.ne (by simp [])
  have run := advance_trans read choice
  refine ⟨t+4,by omega,f,run,fpc,?_,?_,?_,fp.trans bPer,fm.trans bPriv,?_⟩
  · exact (congrArg Fin.val (saved (.inl 2))).trans bTeam
  · exact (congrArg Fin.val (saved (.inr (.inl 2)))).trans bStep
  · exact (saved (.inr (.inr (.inl 0)))).trans bTag
  · intro fuel
    rw [mass_of_advance field M.program run]
    by_cases h : mem z.val = 0
    · have pc : f.pc = exit := by simpa only [ite_eq_left h] using fpc
      obtain ⟨out,opc,sem⟩ := TickIdentity.mass_block field M regions a (idPC L) (idReg reg)
        Fin.elim0 (success L) (fun j => rom (.inr (.inr (.inl j)))) f mem pc fit zero
      have accept : M.code (success L) = .accept := rom (.inr (.inr (.inr (.inl 0))))
      rw [show fuel+25+18*a = (fuel+1)+24+18*a by omega,sem]
      have zeroMarker : initialMemory S hdr (marker (w:=w) regions (phaseNo (clock.phase stepID))).val = 0 := h
      simp only [mass, Machine.program, opc, accept, Instr.run, FieldCode.terminal,
        ite_eq_left zeroMarker, mem]
    · exact (ite_eq_right h).symm


end ThreeFlat.RAM.TickFrontROM

end
end OAI
