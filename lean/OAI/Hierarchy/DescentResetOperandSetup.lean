import OAI.Hierarchy.DescentRetainedSevenRun
import OAI.Hierarchy.DescentResetOperandSetupChart
import OAI.Hierarchy.DescentResetRetainedSetup
import OAI.Hierarchy.DescentResetRetainedPlacement
import OAI.Hierarchy.DescentOperandInputCast
import OAI.Hierarchy.DescentResetRetainedCableLaw
import OAI.Hierarchy.DescentResetOperandSlices

namespace OAI
/-! # The fixed reset-operand setup from the prior libraries to the emitted query tables -/
namespace Hierarchy.DescentResetOperandSetup
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

structure Code (w : ℕ) where
  program : Procedure w
  time : ℕ
  image : Memory w→Memory w

namespace Code
variable {w : ℕ}
def join (a b : Code w) : Code w:=⟨a.program.seq b.program,a.time+b.time,b.image ∘ a.image⟩
structure Runs (a : Code w) (lo hi : ℕ) (m : Memory w) : Prop where
  exec : a.program.Exec m (a.image m) a.time
  cheap : CheapCode a.program
  frame : ∀i,i<lo ∨ hi≤ i → a.image m i=m i

theorem combined {a b : Code w} {lo mid hi : ℕ} {mem : Memory w}
    (left : Runs a lo mid mem) (right : Runs b mid hi (a.image mem))
    (first : lo≤ mid) (last : mid≤hi) : Runs (a.join b) lo hi mem :=by
  refine ⟨?_,cheap_seq left.cheap right.cheap,?_⟩
  · intro P R K board pc reg pub exit installed dat cfg m start same
    exact Procedure.Exec.then left.exec right.exec board pc reg pub exit installed dat cfg m start same
  · intro z h
    exact (right.frame z (h.imp_left (·.trans_le first))).trans (left.frame z (h.imp_right (last.trans ·)))

end Code
namespace Chart
variable (C : Chart)
def placedOld (base : ℕ) :=C.seven.place base
def placedSigned (base : ℕ) :=C.seven.endAddress base
def cable : DescentResetRetainedCableLaw.Shape :=
  ⟨C.oldDegree,C.oldCap,C.retained.donors,C.oldPieces,C.fieldBits,C.queryBits,C.lanes⟩
def width (i : Fin C.inputs) :=if i.val<5 then C.retained.bits else if i.val=5 then 1 else
  if i.val<6+C.strip then C.signedBits else C.ticketBits
theorem width_le (i : Fin C.inputs) : C.width i≤C.sourceWidth :=by
  unfold width sourceWidth
  split_ifs <;> omega

/-- The finite laws are byte-for-byte public. The four rotor inputs and
the bounded fallback stencil are supplied by the preceding reset census. -/
structure Laws where
  rotorQuery : Fin C.members→(Fin 4→Cell C.rotorBits)→Cell C.queryBits
  rotorFields : Fin (7*C.members)→(Fin 4→Cell C.rotorBits)→Cell C.fieldBits
  fallbackQuery : Fin C.members→(Fin C.fallbackInputs→Cell C.fallbackBits)→Cell C.queryBits
  fallbackFields : Fin (7*C.members)→(Fin C.fallbackInputs→Cell C.fallbackBits)→Cell C.fieldBits

structure Sources where
  old : Fin C.retained.sources→Bank
  matrix : Bank
  primary : Fin C.placement.shapes→Bool
  count : Bank
  inverse : Bank
  signed : Fin C.strip→Expr
  which : C.seven.control.Targets
  window : Expr

def previous (base w : ℕ) (s : C.Sources) : Code w:=
  ⟨C.seven.program base w s.which s.primary s.old s.matrix s.window s.count s.inverse,
    C.seven.ticks base w s.which s.old s.matrix s.window s.count s.inverse,
    C.seven.image base s.which s.primary s.old s.matrix s.window s.count s.inverse⟩
def move (b : DescentResetRetainedPlacement.Batch) (base w : ℕ) (s : C.Sources) (keep : Fin C.placement.shapes→Bool) (f : Fin b.fields→Expr) : Code w:=
  ⟨C.placement.code b base w keep f s.count s.inverse,C.placement.ticks b base f s.count s.inverse,
    C.placement.image b base keep f s.count s.inverse⟩
def sources (base w : ℕ) (s : C.Sources) :=
  (C.previous base w s).join (C.move C.signedFields (C.placedSigned base) w s (fun _=>true) s.signed)

def publicBook (base w : ℕ) : Code w :=
  ⟨C.publicCasts.program (C.packetEnd base) w,C.publicCasts.ticks,C.publicCasts.image (C.packetEnd base)⟩

def packetBook (base w : ℕ) : Code w :=
  ⟨C.packets.program (C.placed base) w,C.packets.time (C.placed base) w,C.packets.image (C.placed base)⟩

def castBook (base w : ℕ) : Code w:=⟨DescentOperandInputCast.program C.width C.fieldBits C.sourceWidth C.lanes base w,
  4+10*DescentOperandInputCast.words C.inputs C.sourceWidth C.lanes,
  DescentOperandInputCast.image C.width C.fieldBits C.sourceWidth C.lanes base⟩
def carryBook (base w : ℕ) : Code w:=⟨C.cable.program base w,C.cable.ticks,C.cable.image base⟩
def sliceBook (base w : ℕ) : Code w:=⟨DescentResetOperandSlices.program C.oldPieces C.fieldBits C.lanes base w,
  4+10*(10*2^((C.fieldBits+2)*C.lanes)),DescentResetOperandSlices.image C.oldPieces C.fieldBits C.lanes base⟩
def lawBook {K n a b : ℕ} (f : Fin K→(Fin n→Cell a)→Cell b) (M base w : ℕ) : Code w:=
  ⟨DescentOperandFamilyBook.program f M base w,DescentOperandFamilyBook.ticks K n a M,DescentOperandFamilyBook.image f M base⟩
def beforeFallback (base w : ℕ) (f : C.Laws) :=
  ((((C.castBook (C.publicEnd base) w).join (C.carryBook (C.casts base) w)).join (C.sliceBook (C.slices base) w)).join
    (lawBook f.rotorQuery C.lanes (C.rotorQuery base) w)).join (lawBook f.rotorFields C.lanes (C.rotorFields base) w)
def control (base w : ℕ) (f : C.Laws) :=
  ((C.beforeFallback base w f).join (lawBook f.fallbackQuery C.lanes (C.fallbackQuery base) w)).join
    (lawBook f.fallbackFields C.lanes (C.fallbackFields base) w)
def code (base w : ℕ) (s : C.Sources) (f : C.Laws) :=(((C.sources base w s).join (C.packetBook base w)).join (C.publicBook base w)).join (C.control base w f)

theorem family_run {K n a b w : ℕ} (f : Fin K→(Fin n→Cell a)→Cell b) (M base : ℕ) (mem : Memory w)
    (room : base+words K n a M<2^w) : Code.Runs (lawBook f M base w) base (base+words K n a M) mem :=by
  have go:=DescentOperandFamilyBook.any f M base mem room
  exact ⟨go.1,go.2.1,go.2.2.1⟩

set_option maxHeartbeats 1600000 in
theorem control_run {w : ℕ} (base : ℕ) (m : Memory w) (f : C.Laws) (room : C.endAddress base<2^w) :
    Code.Runs (C.control base w f) (C.publicEnd base) (C.endAddress base) m :=by
  obtain ⟨a,b,c,d,e,h,i,j⟩:=C.order base
  have last:=j.trans_lt room
  have six:=i.trans_lt last
  have five:=h.trans_lt six
  have four:=e.trans_lt five
  have three:=d.trans_lt four
  have two:=(b.trans c).trans_lt three
  have cast:=DescentOperandInputCast.any C.width C.fieldBits C.sourceWidth C.lanes (C.publicEnd base) m C.width_le two
  have first : Code.Runs (C.castBook (C.publicEnd base) w) (C.publicEnd base) (C.casts base) m:=⟨cast.1,cast.2.1,cast.2.2.1⟩
  have carr:=C.cable.any (C.casts base) ((C.castBook (C.publicEnd base) w).image m) three
  have second:=Code.combined first (b:=C.carryBook (C.casts base) w) ⟨carr.1,carr.2.1,carr.2.2⟩ a (b.trans c)
  have cut:=DescentResetOperandSlices.mount_any C.oldPieces C.fieldBits C.lanes (C.slices base) (((C.castBook (C.publicEnd base) w).join (C.carryBook (C.casts base) w)).image m) four
  have third:=Code.combined second (b:=C.sliceBook (C.slices base) w) ⟨cut.1,cut.2.2.2,cut.2.1⟩
    (a.trans (b.trans c)) d
  have fourth:=Code.combined third (family_run f.rotorQuery C.lanes _ _ five) (a.trans (b.trans (c.trans d))) e
  have fifth:=Code.combined fourth (family_run f.rotorFields C.lanes _ _ six) (a.trans (b.trans (c.trans (d.trans e)))) h
  have sixth:=Code.combined fifth (family_run f.fallbackQuery C.lanes _ _ last) (a.trans (b.trans (c.trans (d.trans (e.trans h))))) i
  exact Code.combined sixth (family_run f.fallbackFields C.lanes _ _ room) (a.trans (b.trans (c.trans (d.trans (e.trans (h.trans i)))))) j

structure Ready (s : C.Sources) (w first : ℕ) : Prop where
  packets : C.packets.Fits w (C.placed first)
  lanes : 0<C.lanes
  blocks : 0<C.placement.blocks
  previous : ∀i,(s.old i).Fits w first
  matrix : s.matrix.Fits w first
  count : s.count.Fits w first
  inverse : s.inverse.Fits w first
  signed : ∀i,(s.signed i).Fits w first
  window : s.window.Fits w first

theorem before (base : ℕ) : base≤C.placedOld base ∧ C.placedOld base≤C.placedSigned base ∧
    C.placedSigned base≤C.placed base :=by
  obtain ⟨a,b,d,e,f⟩:=C.seven.intervals base
  have last:=C.placement.affine C.signedFields (C.placedSigned base)
  refine ⟨((a.trans b).trans d).trans e,f,?_⟩
  change C.placedSigned base≤C.placement.endAddress C.signedFields (C.placedSigned base)
  rw [last]
  exact Nat.le_add_right ..

set_option maxHeartbeats 1800000 in
theorem any {w : ℕ} (base : ℕ) (m : Memory w) (s : C.Sources) (f : C.Laws)
    (ready : C.Ready s w base) (room : C.endAddress base<2^w) :
    Code.Runs (C.code base w s f) base (C.endAddress base) m :=by
  obtain ⟨a,b,c⟩:=C.before base
  have post:=C.order base
  have packetOrder : C.placed base ≤ C.packetEnd base := (C.packets.join _).1.trans (C.packets.join _).2
  have publicOrder : C.packetEnd base≤C.publicEnd base:=Nat.le_add_right ..
  have «until» : C.publicEnd base≤C.endAddress base:=by
    obtain ⟨a,b,c,d,e,f,g,h⟩:=post;omega
  have publicFit:=«until».trans_lt room
  have packetFit:=publicOrder.trans_lt publicFit
  have good:=packetOrder.trans_lt packetFit
  have sr:=c.trans_lt good
  have first:=C.seven.any base s.which s.primary s.old s.matrix s.window s.count s.inverse m
    ready.previous ready.matrix ready.window ready.count ready.inverse ready.lanes ready.blocks sr
  have sec : Code.Runs (C.previous base w s) base (C.placedSigned base) m:=⟨first.1,first.2.2,first.2.1⟩
  have cap {a b : ℕ} (L : Bank) (fit : L.Fits w a) (h : a≤b) : L.Fits w b:=⟨fit.1,fit.2.1,fit.2.2.trans h⟩
  have end_:=C.placement.any C.signedFields (C.placedSigned base) (fun _=>true) s.signed s.count s.inverse
    ((C.previous base w s).image m)
    ready.lanes ready.blocks (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (a.trans b) (ready.signed i))
    (cap _ ready.count (a.trans b)) (cap _ ready.inverse (a.trans b)) good
  have source:=Code.combined sec (b:=C.move C.signedFields (C.placedSigned base) w s (fun _=>true) s.signed)
    ⟨end_.1,end_.2.2,end_.2.1⟩ (a.trans b) c
  have pull := C.packets.any (C.placed base) ((C.sources base w s).image m) ready.packets packetFit
  have next := Code.combined source (b:=C.packetBook base w) ⟨pull.1,pull.2.1,pull.2.2⟩ (a.trans (b.trans c)) packetOrder
  have widen:=C.publicCasts.any (C.packetEnd base) (((C.sources base w s).join (C.packetBook base w)).image m) publicFit
  have widened:=Code.combined next (b:=C.publicBook base w) ⟨widen.1,widen.2.1,widen.2.2⟩ ((a.trans (b.trans c)).trans packetOrder) publicOrder
  exact Code.combined widened (C.control_run base _ f room) (((a.trans (b.trans c)).trans packetOrder).trans publicOrder) «until»

end Chart
end
end Hierarchy.DescentResetOperandSetup

end OAI
