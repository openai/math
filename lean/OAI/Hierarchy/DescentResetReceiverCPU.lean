import OAI.Hierarchy.DescentRetiledResetWindow
import OAI.Hierarchy.DescentResetRootAllocator

namespace OAI
/-! # Fixed reset programs from measured stencil and old signed ports through all private roots -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGLNielsen
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local
open DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- All of these dimensions, books and indirect operand instructions are fixed at compilation. -/
structure Receiver (D cap N n r c H G k₀ R M h l t field Ht w : ℕ) where
  origin : ℕ
  saved : Bank
  stencil : Bank
  old : Fin (2*cap)→Fin N→Bank
  slots : G=k₀*(R*M)
  ratio : 0<R
  positive : 0<M

namespace Receiver
variable {D cap N n r c H G k₀ R M h l t field Ht w : ℕ}
 (a : Receiver D cap N n r c H G k₀ R M h l t field Ht w)
local notation "b" => DescentSignedCableCodec.width D cap
local notation "D₀" => 2*cap
local notation "L" => 2^r

def retileEnd := Retile.stop a.origin b H G R M (D₀*N)
def signedOrigin :=joinStop a.retileEnd b N M
def signedChart:=SignedFields.chart a.signedOrigin D₀ H h l b
def signedEnd :=SignedFields.stop a.signedOrigin D₀ H h l b
def tiles (j : Fin D₀) (x : Fin N) : Bank := Retile.output a.origin b H G R M (finProdFinEquiv (j,x))
def tapped (j : Fin D₀) : Bank :=
  ⟨slice (((a.signedChart.chosen (h+l)).bank (schedule (h+l)).length).base) H (2^h) j,Nat.clog 2 (H*2^h)⟩
def lookup (j : Fin (count L cap)) :=spec a.stencil a.tapped t D ((column L cap).symm j)
def atQuery (j : Fin (count L cap)) :=start a.signedEnd (maxBits t D cap L) H (2^c) M j.val
def projectionEnd :=a.signedEnd+stride (maxBits t D cap L) H (2^c) M*count L cap
def endAddress :=(RootTemplates.arena a.projectionEnd H (2^c) M r n D).first (Fintype.card (RootPage r (2^n)))

structure PrefixFits : Prop where
  inputs : ∀j x,(a.old j x).Fits w a.origin
  inputSize : ∀j x,H*chunks G (R*M)≤(a.old j x).size
  retileRoom : a.retileEnd<2^w
  key : a.saved.Fits w a.retileEnd
  signedRoom : a.signedEnd<2^w
  projected : ∀j,(a.lookup j).Room (a.atQuery j) H (2^c) M field w
structure Fits (templates : RootTemplates n r D (2^r) cap) : Prop extends PrefixFits a where
  roots : templates.Fits a.projectionEnd H (2^c) M Ht w

variable {templates : RootTemplates n r D (2^r) cap}

instance : CoeOut (a.Fits templates) a.PrefixFits:=⟨Fits.toPrefixFits⟩

def jobs (space : a.PrefixFits) := fun j=>(a.lookup j).job (a.atQuery j) (space.projected j)
def projected (space : a.PrefixFits) := series (catalog (a.jobs space))
def roots (space : a.Fits templates) :=
  series (catalog (templates.job a.projectionEnd space.roots ∘ (rootIndex r (2^n)).symm))
def signedOp :=joinOp a.retileEnd b N M D₀ (fun j x=>.lookup (a.tiles j x) .row)
def chipCPU :=
  (Book.install (joinGate b N) (joinWidth b N) M w a.retileEnd).seq
    (SignedFields.program a.signedOrigin a.signedChart a.saved a.signedOp D₀ H h l b w)
def chipClock := (4+10*(N*(2*2^(joinWidth b N*M))))+
  SignedFields.duration a.signedOrigin a.signedChart a.saved a.signedOp D₀ H h l b w
def chipImage (mem : Memory w) :=
  SignedFields.image a.signedOrigin a.signedChart a.saved a.signedOp D₀ H h l b
    (Book.image (joinGate b N) (joinWidth b N) M a.retileEnd mem)
def retileCPU :=Retile.program a.origin H b a.slots a.ratio a.positive (incoming a.old) w
def retileClock :=Retile.ticks a.origin H b a.slots a.ratio a.positive (incoming a.old)
def retileImage (mem : Memory w) :=Retile.image a.origin H b a.slots a.ratio a.positive (incoming a.old) mem

/-- The prefix agrees in association with the truthful projected-window execution. -/
def «prefix» (space : a.PrefixFits) := a.retileCPU.seq (a.chipCPU.seq (a.projected space).program)
def prefixTime (space : a.PrefixFits) :=a.retileClock+(a.chipClock+(a.projected space).ticks)
def program (space : a.Fits templates) :=(a.prefix space).seq (a.roots space).program
def ticks (space : a.Fits templates) :=a.prefixTime space+(a.roots space).ticks
def image (space : a.Fits templates) (mem : Memory w) :=
  (a.roots space).image ((a.projected space).image (a.chipImage (a.retileImage mem)))

theorem proj_layout (space : a.PrefixFits) (j : Fin (count L cap)) :
    a.atQuery j≤(a.jobs space j).first ∧ (a.jobs space j).limit≤a.signedEnd+
      stride (maxBits t D cap L) H (2^c) M*(j.val+1) := by
  obtain ⟨lower,upper⟩:=(a.lookup j).bounds (a.atQuery j) (space.projected j)
  exact ⟨lower.ge,upper.le.trans (extent _ _ _ j (word_bound _ _ _))⟩

def prefixImage (space : a.PrefixFits) (mem : Memory w) :=
  (a.projected space).image (a.chipImage (a.retileImage mem))

theorem prefix_hardware (space : a.PrefixFits) (mem : Memory w) :
    (a.prefix space).Exec mem (a.prefixImage space mem) (a.prefixTime space) ∧ CheapCode (a.prefix space) ∧
    ∀x,x<a.origin ∨ a.projectionEnd≤x→a.prefixImage space mem x=mem x := by
  obtain ⟨ret,cheapR,retKeep⟩:=Retile.runs (a:=b) a.origin a.slots a.ratio a.positive (incoming a.old)
    (fun _=>space.inputs _ _) (fun _=>space.inputSize _ _) space.retileRoom mem
  have source (j : Fin D₀) (x : Fin N) : (Expr.lookup (a.tiles j x) .row).Fits w a.retileEnd :=
    ⟨(Retile.fits_output a.origin (finProdFinEquiv (j,x)) space.retileRoom).1,trivial⟩
  obtain ⟨shuffle,cheapS,shuffleKeep⟩:=from_slots_any («b»:=b) (M:=M) (h:=h) (l:=l) (H:=H) a.retileEnd
    a.saved (fun j x=>Expr.lookup (a.tiles j x) .row) (a.retileImage mem) source space.key space.signedRoom
  obtain ⟨columns,_,_,projectKeep⟩:=issued_catalog (a.jobs space) a.signedEnd
    (stride (maxBits t D cap L) H (2^c) M) (a.proj_layout space) (a.chipImage (a.retileImage mem))
  refine ⟨ret.then (shuffle.then columns),cheap_seq cheapR (cheap_seq cheapS (a.projected space).cheap),?_⟩
  have h₀:a.origin≤a.retileEnd:=by dsimp [retileEnd,Retile.stop,Subwords.destination];omega
  have h₁:a.retileEnd≤a.signedOrigin:=Nat.le_add_right ..
  have h₂:a.signedOrigin≤a.signedEnd:=Dated.origin_le_endAddress _ _ _ _ _
  have h₃:a.signedEnd≤a.projectionEnd:=Nat.le_add_right ..
  rintro x (lo|hi)
  · have l:=lo.trans_le h₀
    exact (projectKeep x (.inl (l.trans_le (h₁.trans h₂)))).trans
      ((shuffleKeep x (.inl l)).trans (retKeep x (.inl lo)))
  · exact (projectKeep x (.inr hi)).trans ((shuffleKeep x (.inr (h₃.trans hi))).trans
      (retKeep x (.inr ((h₁.trans h₂).trans (h₃.trans hi)))))

theorem prefix_run (space : a.PrefixFits) (mem : Memory w) :
    (a.prefix space).Exec mem (a.prefixImage space mem) (a.prefixTime space) :=(a.prefix_hardware space mem).1

theorem root_result (space : a.Fits templates) (mem : Memory w) (p : RootPage r (2^n)) (x : ℕ)
    (lo : (templates.job a.projectionEnd space.roots p).first≤x)
    (hi : x<(templates.job a.projectionEnd space.roots p).limit) :
    a.image space mem x=(templates.job a.projectionEnd space.roots p).image (a.prefixImage space mem) x :=
  (templates.run a.projectionEnd space.roots (a.prefixImage space mem)).2.1 p x lo hi

theorem kept_prefix (space : a.Fits templates) (mem : Memory w) (x : ℕ) (lo : x<a.projectionEnd) :
    a.image space mem x=a.prefixImage space mem x :=
  (templates.run a.projectionEnd space.roots (a.prefixImage space mem)).2.2 x (.inl lo)

theorem any_input (space : a.Fits templates) (mem : Memory w) :
    (a.program space).Exec mem (a.image space mem) (a.ticks space) ∧
      CheapCode (a.program space) ∧
      ∀x,x<a.origin ∨ a.endAddress≤x→a.image space mem x=mem x := by
  obtain ⟨ret,cheapR,retKeep⟩:=Retile.runs (a:=b) a.origin a.slots a.ratio a.positive (incoming a.old)
    (fun _=>space.inputs _ _) (fun _=>space.inputSize _ _) space.retileRoom mem
  have source (j : Fin D₀) (x : Fin N) : (Expr.lookup (a.tiles j x) .row).Fits w a.retileEnd :=
    ⟨(Retile.fits_output a.origin (finProdFinEquiv (j,x)) space.retileRoom).1,trivial⟩
  obtain ⟨shuffle,cheapS,shuffleKeep⟩:=from_slots_any («b»:=b) (M:=M) (h:=h) (l:=l) (H:=H) a.retileEnd
    a.saved (fun j x=>Expr.lookup (a.tiles j x) .row) (a.retileImage mem) source space.key space.signedRoom
  obtain ⟨columns,_,_,projectKeep⟩:=issued_catalog (a.jobs space) a.signedEnd
    (stride (maxBits t D cap L) H (2^c) M) (a.proj_layout space) (a.chipImage (a.retileImage mem))
  obtain ⟨devices,_,deviceKeep⟩:=templates.run a.projectionEnd space.roots
    ((a.projected space).image (a.chipImage (a.retileImage mem)))
  refine ⟨Procedure.Exec.then (a.prefix_run space mem) (@devices),
    cheap_seq (cheap_seq cheapR (cheap_seq cheapS (a.projected space).cheap)) (a.roots space).cheap,?_⟩
  have first : a.origin≤a.retileEnd:=by dsimp [retileEnd,Retile.stop,Subwords.destination];omega
  have signedBase : a.retileEnd≤a.signedOrigin:=Nat.le_add_right ..
  have second : a.signedOrigin≤a.signedEnd:=Dated.origin_le_endAddress _ _ _ _ _
  have third : a.signedEnd≤a.projectionEnd:=Nat.le_add_right ..
  have last : a.projectionEnd≤a.endAddress:=Nat.le_add_right ..
  rintro x (lo|hi)
  · have a₁:=lo.trans_le first
    have a₂:=a₁.trans_le (signedBase.trans second)
    exact (deviceKeep _ (.inl (a₂.trans_le third))).trans ((projectKeep _ (.inl a₂)).trans
      ((shuffleKeep _ (.inl a₁)).trans (retKeep _ (.inl lo))))
  · have a₃:=last.trans hi
    have a₂:=third.trans a₃
    exact (deviceKeep _ (.inr hi)).trans ((projectKeep _ (.inr a₃)).trans
      ((shuffleKeep _ (.inr a₂)).trans (retKeep _ (.inr (signedBase.trans (second.trans a₂))))))

end Receiver
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
