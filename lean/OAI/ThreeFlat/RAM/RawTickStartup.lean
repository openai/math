import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalTraceSource
import OAI.ThreeFlat.RAM.RawTickSpace

namespace OAI
/-! # Three native preprocessing loops from short metadata bits to a trivalent trace layout -/

namespace ThreeFlat.RAM.RawTickStartup

open Computability.VPVNP.BurstRAM Diagonal.TraceAddressRecord PhysicalProcedure PhysicalInputPhases
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Fintype F] [CommSemiring F] {w q t b p : ℕ} (G : BitNetwork F q)
    (code : FieldCode F w) (records : Fin q → Record) (input : Fin t → Fin q → BitSource b p)
    (src raw packedBase : ℕ)
local notation "X" => PhysicalTraceSource.expanded G input
local notation "P" => RawTickBuilder.contiguous X raw
local notation "n" => FixedTraceImage.count G
local notation "term" => FixedTraceProgram.program w
local notation "portBase" => packedBase+11*G.cells

def data : Fin FixedTraceProgram.P → Word w :=
  Fin.addCases (fun _ : Fin 2 => 0) (Fin.addCases (fun _ : Fin 5 => 0)
    (FixedTraceProgram.publicWords G code p b raw packedBase portBase))

omit [Fintype F] in
theorem operands (i : Fin 11) : data (p:=p) (b:=b) G code raw packedBase (FixedTraceProgram.extra i) =
    FixedTraceProgram.publicWords G code p b raw packedBase portBase i := by
  simp only [data,FixedTraceProgram.extra,Fin.addCases_right]

def procedure : Procedure w :=
  ((packing w src packedBase n).seq
    (writing term (data (p:=p) (b:=b) G code raw packedBase) raw (11*(X).cells))).seq
    (TickLinkRows.builder w P)

def cost := (n*(5*w+6)+6 + (4+11*(X).cells*(2*(term).binds+4)))+
  (9+17*(RawTick.sources (X).internal p)+26*RawTick.sockets (X).cells)

structure Fits : Prop where
  apart : packedBase+n ≤ src ∨ src+w*n ≤ packedBase
  packedEnd : packedBase+n < 2^w
  bitEnd : src+w*n < 2^w
  rawBefore : raw+11*(X).cells ≤ packedBase
  links : (P).Fits w
  sourceBound : 2+q+G.internal<2^w
  cellBound : G.cells<2^w

theorem run (fit : Fits (w:=w) G input src raw packedBase)
    (safe : ∀ (v : Fin t) j,(records j).Fits w v.val)
    (addr : ∀ (v : Fin t) j,(records j).eval v.val=BitLayout.sourceAddress (input v j)) :
    (procedure G code input src raw packedBase).Spec
      (fun m => ∀ i,m (src+i.val)=((FixedTraceImage.parameter G code records i).toNat : Word w))
      (fun start out =>
        let packed := FixedTraceImage.packed G code records packedBase start
        let source := fillSegment raw (11*(X).cells) (PhysicalTraceSource.rowWord X code raw) packed
        RawTickBuilder.loaded X code raw source ∧
          RawTickBuilder.Result X raw (P).lastBase (P).prevBase (P).dstBase source out)
      (cost (w:=w) G input) := by
  let A := packing w src packedBase n
  let B := writing term (data (p:=p) (b:=b) G code raw packedBase) raw (11*(X).cells)
  let srcWord := PhysicalTraceSource.rowWord X code raw
  let Pkt := FixedTraceImage.packed G code records packedBase
  let Ready (m : Memory w) := ∃ fromMem, m=Pkt fromMem
  let rowWords := 11*(X).cells
  have cap := fit.bitEnd
  have sep := fit.packedEnd
  have lo := fit.rawBefore
  have destFit : raw+11*(X).cells < 2^w := lo.trans_lt ((Nat.le_add_right _ _).trans_lt sep)
  have gateFit : packedBase+11*G.cells ≤ 2^w := by unfold FixedTraceImage.count at sep; omega
  have portFit : portBase+11*q ≤ 2^w := by unfold FixedTraceImage.count at sep; omega
  have wa : A.Spec _ _ _ := packing_spec_disjoint G code records src packedBase fit.apart fit.packedEnd fit.bitEnd
  have wb : B.Spec Ready (fun m o => o=fillSegment raw rowWords srcWord m)
      (4+rowWords*(2*(term).binds+4)) := by
    apply writing_spec _ _ _ _ destFit
    rintro m ⟨old,rfl⟩
    exact PhysicalTraceSource.row_correct G code records input raw packedBase portBase
      (data (p:=p) (b:=b) G code raw packedBase) _ (operands G code raw packedBase)
      (FixedTraceImage.packed_gate G code records packedBase old)
      (FixedTraceImage.packed_port G code records packedBase old) lo (lo.trans (Nat.le_add_right _ _)) destFit
      gateFit portFit safe addr fit.sourceBound fit.cellBound fit.links.literal
  have ab : (A.seq B).Spec _ _ _ := Procedure.Spec.seq wa wb (fun m o h => ⟨m,h⟩)
  have loaded (m : Memory w) : RawTickBuilder.loaded X code raw (fillSegment raw rowWords srcWord m) :=
    PhysicalTraceSource.generated_at G code input raw m
  have bc : (TickLinkRows.builder w P).Spec _ _ _ := RawTickBuilder.build X raw (P).lastBase (P).prevBase (P).dstBase code fit.links
  have all : ((A.seq B).seq (TickLinkRows.builder w P)).Spec _ _ _ :=
    Procedure.Spec.seq ab bc (by
      rintro m o ⟨temp,_,rfl⟩
      exact loaded temp)
  intro pcs regs pubs M pc reg pub exit installed data c m start bits
  obtain ⟨steps,time,final,out,run,returned,h⟩ := all M pc reg pub exit installed data c m start bits
  obtain ⟨s,⟨tmp,rfl,rfl⟩,good⟩ := h
  exact ⟨steps,time,final,out,run,returned,loaded _,good⟩

end
end ThreeFlat.RAM.RawTickStartup

end OAI
