import OAI.Hierarchy.DescentResetRetileStrip
import OAI.Hierarchy.DescentPackedNodeDigit
import OAI.Hierarchy.DescentSignedGLTotal

namespace OAI
/-! # One physically saved matrix changes basis on all prior reset operand books -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGLPacked.BankImage DescentGLNielsen
open DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : Layout)

def channelID (f : Fin v.fields) (n : Fin v.previousNodes) : Fin v.channels :=finProdFinEquiv (f,n)
def retiled (base : ℕ) (p : Fin v.sources) := Strip.bank base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord p.val
def oldScalar (base : ℕ) (j : Fin v.channels) (b : Fin v.blocks) : Expr :=
  let z:=(finProdFinEquiv.symm j : Fin v.fields×Fin v.previousNodes)
  ScalarOperand.project (ScalarOperand.chart (v.digits base) v.bits v.previousNodes v.gatherLanes)
    (.lookup (v.retiled base (v.sourceID z.1 b)) .row) z.2
def firstCode (base w : ℕ) (old : Fin v.sources→Bank) :=
  Strip.code base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord w old
def digitDict (base : ℕ) :=ROM.mount (ScalarOperand.pages v.bits v.previousNodes v.gatherLanes)
  (v.wholeWord*v.gatherLanes) w (v.digits base)
def digitImage (base : ℕ) (old : Fin v.sources→Bank) (m : Memory w) :=ROM.after
  (ScalarOperand.pages v.bits v.previousNodes v.gatherLanes) (v.wholeWord*v.gatherLanes) (v.digits base)
  ((v.firstCode base w old).image m)
def blockDict (base w : ℕ) :=Book.install (SignedFields.joinGate v.bits v.blocks)
  (SignedFields.joinWidth v.bits v.blocks) v.gatherLanes w (v.slots base)
def blockImage (base : ℕ) (m : Memory w) :=Book.image (SignedFields.joinGate v.bits v.blocks)
  (SignedFields.joinWidth v.bits v.blocks) v.gatherLanes (v.slots base) m
def chart (base : ℕ) :=SignedFields.chart (v.matrix base) v.channels v.hosts v.high v.low v.bits
def joined (base : ℕ) :=SignedFields.joinOp (v.slots base) v.bits v.blocks v.gatherLanes v.channels (v.oldScalar base)
def basisCode (base w : ℕ) (saved : Bank) :=SignedFields.program (v.matrix base) (v.chart base) saved
  (v.joined base) v.channels v.hosts v.high v.low v.bits w
def basisProgram (base w : ℕ) (old : Fin v.sources→Bank) (saved : Bank) :=
  ((v.firstCode base w old).program.seq (v.digitDict (w:=w) base)).seq ((v.blockDict base w).seq (v.basisCode base w saved))
def basisTicks (base w : ℕ) (old : Fin v.sources→Bank) (saved : Bank) :=
  ((v.firstCode base w old).ticks+(4+10*(v.previousNodes*2^(v.wholeWord*v.gatherLanes))))+
  ((4+10*(v.blocks*(2*2^(SignedFields.joinWidth v.bits v.blocks*v.gatherLanes))))+
   SignedFields.duration (v.matrix base) (v.chart base) saved (v.joined base) v.channels v.hosts v.high v.low v.bits w)
def basisImage (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w) :=
  SignedFields.image (v.matrix base) (v.chart base) saved (v.joined base) v.channels v.hosts v.high v.low v.bits
    (v.blockImage base (v.digitImage base old m))

theorem basis_any (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w)
    (orig : ∀i,(old i).Fits w base) (key : saved.Fits w base) (room : v.mixed base<2^w) :
    (v.basisProgram base w old saved).Exec m (v.basisImage base old saved m) (v.basisTicks base w old saved) ∧
    (∀x,x<base ∨ v.mixed base≤x→v.basisImage base old saved m x=m x) ∧ CheapCode (v.basisProgram base w old saved) :=by
  obtain ⟨lo,du,gd,done_,_⟩:=v.order base
  have before:=lo.trans du
  have wide:=du.trans_lt (gd.trans_lt (done_.trans_lt room))
  obtain ⟨start,frame1⟩:=Strip.any base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord old m orig wide
  obtain ⟨digit,_⟩:=ROM.run (ScalarOperand.pages v.bits v.previousNodes v.gatherLanes)
    (v.wholeWord*v.gatherLanes) (v.digits base) ((v.firstCode base w old).image m) (gd.trans_lt (done_.trans_lt room))
  have sf (i : Fin v.channels) (b : Fin v.blocks) : (v.oldScalar base i b).Fits w (v.slots base):=by
    let z:=(finProdFinEquiv.symm i : Fin v.fields×Fin v.previousNodes)
    have prior:=(Strip.fits (w:=w) base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord (v.sourceID z.1 b) wide).1
    have stat:=ROM.bank_room (ScalarOperand.pages v.bits v.previousNodes v.gatherLanes) (v.wholeWord*v.gatherLanes)
      (v.digits base) (v.slots base) z.2 le_rfl le_rfl (gd.trans_lt (done_.trans_lt room))
    exact ⟨stat,⟨⟨prior.1,prior.2.1,prior.2.2.trans du⟩,trivial⟩⟩
  obtain ⟨ret,cheap,frame2⟩:=SignedFields.from_slots_any (D:=v.channels) (H:=v.hosts) (h:=v.high) (l:=v.low)
    (b:=v.bits) (M:=v.gatherLanes) (v.slots base) saved (v.oldScalar base) (v.digitImage base old m) sf
    ⟨key.1,key.2.1,key.2.2.trans before⟩ room
  refine ⟨Procedure.Exec.then (Procedure.Exec.then start digit) ret,?_,?_⟩
  · intro x away
    exact (frame2 x (away.imp_left (fun h=>h.trans_le before))).trans
      ((ROM.frame _ _ _ _ x (away.imp (fun h=>h.trans_le lo) (fun h=>(gd.trans done_).trans h))).trans
       (frame1 x (away.imp_right (fun h=>(du.trans (gd.trans done_)).trans h))))
  · exact cheap_seq (cheap_seq (NativePhase.cheap _) (ROM.cheap _ _ _ _)) cheap

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
