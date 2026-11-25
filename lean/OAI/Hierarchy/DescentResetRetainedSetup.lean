import OAI.Hierarchy.DescentResetRetainedMixer
import OAI.Hierarchy.DescentResetRetainedDecoder
import OAI.Hierarchy.DescentResetNodeBooks

namespace OAI
/-! # One fixed native reset program for immutable argument words and local private names -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : Layout)

def outputID (mode : Fin 2) (f : Fin 7) (arg : Fin v.args) (node : Fin v.nodes) : Fin v.outputs :=
  finSumFinEquiv (.inl (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (mode,f),arg),node)))
def donorID (node : Fin v.nodes) : Fin v.outputs :=finSumFinEquiv (.inr node)
def function (i : Fin v.outputs) (x : Cell v.siteWord) : Cell v.bits :=
  match (finSumFinEquiv.symm i : Fin ((2*7*v.args)*v.nodes) ⊕ Fin v.nodes) with
  | .inl j=>
    let q:=(finProdFinEquiv.symm j : Fin (2*7*v.args)×Fin v.nodes)
    let p:=(finProdFinEquiv.symm q.1 : Fin (2*7)×Fin v.args)
    let f:=(finProdFinEquiv.symm p.1 : Fin 2×Fin 7)
    v.decodeDigit x f.1 f.2 p.2 q.2
  | .inr n=>v.donorDigit x n.val
def wordPages (i : Fin v.outputs) : ROM.Page :=
  ⟨v.siteWord*v.decodedLanes,fun x=>(DescentSIMDLookup.table (M:=v.decodedLanes) (v.function i) x).val⟩
def dictionary (base : ℕ) (i : Fin v.outputs) :=ROM.bank v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) i
def joinTables (base : ℕ) :=DescentResetNodeBooks.tabs (v.tables base) v.stripWord v.channels v.decodedLanes
def oldSite (base : ℕ) :=Gather.assembly (v.joinTables base) (fun j=>.lookup (v.hostBank base j) .row)
def readTerm (base p : ℕ) : Expr :=if hi:p<v.outputs then .lookup (v.dictionary base ⟨p,hi⟩) (v.oldSite base) else .lit 0
def scans (base : ℕ) :=DescentPackedFlowBatch.passes (v.out base) v.rows v.rows (v.readTerm base) 0 v.outputs
def joinedPages (base w : ℕ) :=ROM.mount (DescentResetNodeBooks.page v.stripWord v.channels v.decodedLanes)
   ((v.siteWord+v.stripWord)*v.decodedLanes) w (v.tables base)
def joinedImage (base : ℕ) (m : Memory w) :=ROM.after (DescentResetNodeBooks.page v.stripWord v.channels v.decodedLanes)
   ((v.siteWord+v.stripWord)*v.decodedLanes) (v.tables base) m
def looked (base : ℕ) (m : Memory w) :=ROM.after v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) (v.joinedImage base m)
def originalOutput (base : ℕ) (i : Fin v.outputs) : Bank :=
  ⟨v.out base+i.val*v.rows,Nat.clog 2 (v.rows+1)⟩
def final (base w : ℕ) :=Strip.code (v.reissue base) v.hosts v.grouped v.decodedLanes v.emitLanes v.bits w (v.originalOutput base)
def bank (base : ℕ) (i : Fin v.outputs) :=Strip.bank (v.reissue base) v.hosts v.grouped v.decodedLanes v.emitLanes v.bits i.val
def operand (base : ℕ) (kind : Fin 2) (f : Fin 7) (arg : Fin v.args) (node : Fin v.nodes) : Expr :=
  .lookup (v.bank base (v.outputID kind f arg node)) .row
def donorOrdinal (base : ℕ) (node : Fin v.nodes) : Expr :=.lookup (v.bank base (v.donorID node)) .row
def writeCode (base w : ℕ) := ((v.joinedPages base w).seq
  (ROM.mount v.wordPages (v.siteWord*v.decodedLanes) w (v.decode base))).seq (ProtocolRAM.program w (v.scans base))
def writeTicks (base : ℕ) := ((4+10*((v.channels+1)*2^((v.siteWord+v.stripWord)*v.decodedLanes)))+
  (4+10*(v.outputs*2^(v.siteWord*v.decodedLanes))))+clock (v.scans base)
def writeImage (base : ℕ) (m : Memory w) :=result (v.scans base) (v.looked base m)
def program (base w : ℕ) (old : Fin v.sources→Bank) (key : Bank) :=
  ((v.moved base w old key).seq (v.writeCode base w)).seq (v.final base w).program
def ticks (base w : ℕ) (old : Fin v.sources→Bank) (key : Bank) :=
  (v.movedTicks base w old key+v.writeTicks base)+(v.final base w).ticks
def image (base : ℕ) (old : Fin v.sources→Bank) (key : Bank) (m : Memory w) :=
  (v.final base w).image (v.writeImage base (v.movedImage base old key m))

theorem validOutput (base : ℕ) (i : Fin v.outputs) (space : v.reissue base<2^w) :
    (v.originalOutput base i).Fits w (v.reissue base) ∧ v.rows≤(v.originalOutput base i).size :=by
  have seq:=Nat.mul_le_mul_right v.rows i.isLt.le
  have end_ : (v.originalOutput base i).base+(v.originalOutput base i).size≤v.reissue base:=by
    change v.out base+i.val*v.rows+2^Nat.clog 2 (v.rows+1)≤v.out base+v.outputs*v.rows+2^Nat.clog 2 (v.rows+1)
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (end_.trans_lt space),end_⟩,DescentResetNodeBooks.capacity _⟩

theorem joinBounds (base : ℕ) (space : v.out base<2^w) : Gather.Bounds (w:=w) (d:=v.stripWord) (M:=v.decodedLanes)
    (v.joinTables base) (fun j=>.lookup (v.hostBank base j) .row) (v.out base) :=by
  obtain ⟨_,_,_,_,_,lo,hi,_⟩:=v.order base
  have cut:=lo.trans hi
  intro j
  have prev:=(Strip.fits (w:=w) (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord j (cut.trans_lt space)).1
  have tab:=ROM.bank_room (w:=w) (DescentResetNodeBooks.page v.stripWord v.channels v.decodedLanes)
      ((v.siteWord+v.stripWord)*v.decodedLanes) (v.tables base) (v.out base)
  have safe (i : Fin (v.channels+1)) :=tab i (DescentResetNodeBooks.page_bits ..) hi space
  exact ⟨⟨⟨prev.1,prev.2.1,prev.2.2.trans cut⟩,trivial⟩,safe 0,safe j.succ,rfl,rfl⟩

theorem readFits (base : ℕ) (j : ℕ) (inside : j<v.outputs) (space : v.out base<2^w) : (v.readTerm base j).Fits w (v.out base) :=by
  rw [readTerm,dite_eq_left inside]
  exact ⟨ROM.bank_room v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) (v.out base) ⟨j,inside⟩ le_rfl le_rfl space,
    Gather.fits _ _ _ (v.joinBounds base space) _⟩

theorem writes (base : ℕ) (m : Memory w) (space : v.reissue base<2^w) :
    (v.writeCode base w).Exec m (v.writeImage base m) (v.writeTicks base) ∧
    (∀a,a<v.tables base ∨ v.reissue base≤a→v.writeImage base m a=m a) ∧ CheapCode (v.writeCode base w) :=by
  obtain ⟨_,_,_,_,_,one,two,three,_⟩:=v.order base
  have fin : v.out base+v.outputs*v.rows≤v.reissue base:=Nat.le_add_right ..
  have outRoom:=three.trans_lt space
  obtain ⟨tab,_⟩:=ROM.run (DescentResetNodeBooks.page v.stripWord v.channels v.decodedLanes)
      ((v.siteWord+v.stripWord)*v.decodedLanes) (v.tables base) m (two.trans_lt outRoom)
  obtain ⟨dict,_⟩:=ROM.run v.wordPages (v.siteWord*v.decodedLanes) (v.decode base) (v.joinedImage base m) outRoom
  obtain ⟨write,_,low⟩:=DescentPackedFlowBatch.execute (v.out base) v.rows v.rows v.outputs (v.readTerm base) (v.looked base m)
    (fun j hj=>v.readFits base j hj outRoom) (fin.trans_lt space) le_rfl
  refine ⟨Procedure.Exec.then (Procedure.Exec.then tab dict) write,?_,cheap_seq (cheap_seq (ROM.cheap _ _ _ _) (ROM.cheap _ _ _ _)) (@ProtocolRAM.program_cheap _ _)⟩
  intro addr h
  have frame : v.looked base m addr=m addr:=(ROM.frame _ _ _ _ _ (h.imp (fun e=>e.trans_le one)
    (fun e=>three.trans e))).trans (ROM.frame _ _ _ _ _ (h.imp_right (fun e=>(two.trans three).trans e)))
  rcases h with h|h
  · exact (low addr (h.trans_le (one.trans two))).trans frame
  · exact (DescentPackedFlowBatch.above _ _ _ _ _ 0 v.outputs addr le_rfl
      (by simpa only [Nat.zero_add] using fin.trans h)).trans frame

theorem any (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w)
    (prior : ∀i,(old i).Fits w base) (key : saved.Fits w base) (space : v.endAddress base<2^w) :
    (v.program base w old saved).Exec m (v.image base old saved m) (v.ticks base w old saved) ∧
    (∀a,a<base ∨ v.endAddress base≤a→v.image base old saved m a=m a) ∧ CheapCode (v.program base w old saved) :=by
  obtain ⟨a,b,c,d,e,f,g,h,i⟩:=v.order base
  have early:=a.trans (b.trans (c.trans (d.trans e)))
  have next:=f.trans (g.trans h)
  obtain ⟨move,frameM,cheapM⟩:=v.moved_any base old saved m prior key ((next.trans i).trans_lt space)
  obtain ⟨write,frameW,cheapW⟩:=v.writes base (v.movedImage base old saved m) (i.trans_lt space)
  obtain ⟨finish,frameF⟩:=Strip.any (v.reissue base) v.hosts v.grouped v.decodedLanes v.emitLanes v.bits
    (v.originalOutput base) (v.writeImage base (v.movedImage base old saved m))
    (fun j=>(v.validOutput base j (i.trans_lt space)).1) space
  refine ⟨Procedure.Exec.then (Procedure.Exec.then move write) finish,?_,cheap_seq (cheap_seq cheapM cheapW) (NativePhase.cheap _)⟩
  intro u hx
  exact (frameF u (hx.imp_left (fun z=>z.trans_le (early.trans next)))).trans
    ((frameW u (hx.imp (fun z=>z.trans_le early) (fun z=>i.trans z))).trans
     (frameM u (hx.imp_right (fun z=>(next.trans i).trans z))))

theorem returned (base : ℕ) (i : Fin v.outputs) (room : v.endAddress base<2^w) :
    (v.bank base i).Fits w (v.endAddress base) ∧ v.hosts*chunks v.grouped v.emitLanes≤(v.bank base i).size :=
  Strip.fits (w:=w) (v.reissue base) v.hosts v.grouped v.decodedLanes v.emitLanes v.bits i room

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
