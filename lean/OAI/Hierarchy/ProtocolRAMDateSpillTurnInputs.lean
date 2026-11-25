import OAI.Hierarchy.ProtocolRAMDateSpillTurnRun

namespace OAI
/-! # Original archived operands for each dated live-turn publisher -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.DateSpill.TurnPage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnChart ProtocolRAMTurnItinerary Calendar
open scoped Classical Fin.CommRing

variable {W roles : ℕ} (P : TurnPage roles)
local notation "T" => P.terminal
local notation "L" => P.window
local notation "d" => P.data
local notation "b" => P.banks
local notation "oldBanks" => [(b).oldSource,(b).oldTarget,(b).edge,(b).tailSite,(b).tailRole,(b).headRole,(b).starts]
local notation "valueAt" m => ProtocolRAMTurnSnapshot.values P.banks m

structure Inputs (cut : ℕ) (m : Memory W) where
  u : Fin (T).turns→Geometry
  w : Words
  sitesAt : Fin (T).turns→ℕ
  oldBase : ℕ→ℕ
  newBase : ℕ→ℕ
  leftSafe : P.left.prefix.Fits W cut
  rightSafe : P.right.prefix.Fits W cut
  original : ∀f (i : ℕ),i<2^(T).romBits→(ProtocolRAMTurnDirectory.bank (T).rom (T).romBits f).read m (i:Word W)=
      ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base f i
  romLow : (T).rom+4*2^(T).romBits≤cut
  oldBaseLow : (T).base≤P.base
  bits : (T).romBits=(L).romBits
  headerLow : (T).header+6*2^(T).headerBits≤cut
  «public» : Loaded (T).header (T).headerBits u m
  safe : ProtocolRAMTurnCursor.Safe (d) W cut
  bank : ∀a∈(T).heads::oldBanks,a.Fits W cut
  old : ∀i,0<w.width (u i).item→(d).At w m (u i)
  weights : ∀i,(d).oldWidth.read m ((u i).item:Word W)=(w.width (u i).item:Word W)
  within : ∀i,(u i).raw≤(u i).length
  lengthFit : ∀i,(u i).length<2^W
  posPrev : ∀i:Fin (T).turns,0<(u i).raw→0 < i.val
  closed : ∀i:Fin (T).turns,0<(u i).raw→0<w.width (u i).item→
      0<w.width (u ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩).item
  endpoint : ∀i,0<w.width (u i).item→(ProtocolRAMVisitColumns.total P.walk).eval m (i.val:Word W)=
      (sitesAt i:Word W)+ProtocolRAMTurnWalk.carried (fun j=>(sitesAt j:Word W)) i
        (ProtocolRAMVisitColumns.previous? (fun j=>(u j).raw) posPrev i)
  siteFits : ∀i,0<w.width (u i).item→sitesAt i<2^W
  left : ∀i,0<w.width (u i).item→∀s,(record u w sitesAt i).boundary s→
      (u i).item<P.ranks.old ∧ P.left.prefix.eval m ((u i).item:Word W)=(oldBase (u i).item:Word W)
  right : ∀i,0<w.width (u i).item→∀s,¬(record u w sitesAt i).boundary s→
      let eid:=(valueAt m).edge ((record u w sitesAt i).occurrence s)
      eid<P.ranks.edges ∧ P.right.prefix.eval m (eid:Word W)=(newBase eid:Word W)
  put : ProtocolRAMTurnShelf.Live (fun i=>Turns.fieldWords (record u w sitesAt i) (valueAt m) oldBase newBase) ↪
      ProtocolRAMTurnShelf.Seats (T).sites (T).seats
  loc : ∀z,(put z).1.val=(record u w sitesAt z.val).site ∧ (put z).2.val=(record u w sitesAt z.val).seat
  widthFit : ∀i,(record u w sitesAt i).width<2^W

namespace Inputs
variable {P} {cut : ℕ} {m : Memory W} (R : P.Inputs cut m)

def columns (i : Fin (T).turns) :=
  Turns.fieldWords (record R.u R.w R.sitesAt i) (valueAt m) R.oldBase R.newBase

def word (f : Fin 5) (s : ProtocolRAMTurnShelf.Seats (T).sites (T).seats) : Word W :=
  ProtocolRAMTurnShelf.entry R.columns R.put f s

theorem run (state : Memory W) (common : ∀a<cut,state a=m a) (below : cut≤P.first) (room : P.stop≤2^W) :
    ∃out,(P.program W).Exec state out P.ticks ∧
      (∀(f : Fin 5) (s : ProtocolRAMTurnShelf.Seats (T).sites (T).seats),
        out (P.base+f.val*((T).sites*(T).seats)+s.1.val*(T).seats+s.2.val)=R.word f s) ∧
      ∀a,a<P.first ∨ P.stop≤a→ out a=state a :=
  P.run_from cut R.u R.w R.sitesAt R.oldBase R.newBase m state common below R.leftSafe R.rightSafe R.original
    R.romLow R.oldBaseLow R.bits room R.headerLow R.public R.safe R.bank R.old R.weights R.within
    R.lengthFit R.posPrev R.closed R.endpoint R.siteFits R.left R.right R.put R.loc R.widthFit
end Inputs
end Hierarchy.ProtocolRAM.DateSpill.TurnPage

end
end OAI
