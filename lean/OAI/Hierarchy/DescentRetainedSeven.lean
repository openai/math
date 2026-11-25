import OAI.Hierarchy.DescentRetainedSevenChart
import OAI.Hierarchy.DescentRetainedControlRead
import OAI.Hierarchy.DescentRetainedTargetPlacementRead
import OAI.Hierarchy.DescentResetRetainedRead

namespace OAI
/-! # Produce every retained reset pointer from chronologically sorted, home-filtered predecessors -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentPackedColony
open DescentPacking.PackedMatch.Local DescentSixParty.Chronology DescentResetRetainedSetup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w : ℕ} (c : DescentRetainedSeven.Chart)
local notation "L" => c.retained

def joined (floor : ℕ) (which : c.control.Targets) (t : Fin c.placement.shapes) : Expr:=
  Gather.assembly (DescentResetNodeBooks.tabs (c.tabs floor) (L).stripWord (L).channels (L).decodedLanes)
    (fun j=>c.control.targetStream which (c.seen floor) t (.lookup ((L).hostBank floor j) .row))

def dictionary (floor : ℕ) (o : Fin (L).outputs) :=
  ROM.bank (L).wordPages ((L).siteWord*(L).decodedLanes) (c.lookup floor) o

def query (floor : ℕ) (which : c.control.Targets) (o : Fin (L).outputs) (t : Fin c.placement.shapes) : Expr :=
  let word:=Expr.lookup (c.dictionary floor o) (c.joined floor which t)
  match (finSumFinEquiv.symm o : Fin ((2*7*(L).args)*(L).nodes) ⊕ Fin (L).nodes) with
  | .inl _=>word
  | .inr _=>c.control.originalID which (c.seen floor) t word

def terms (floor : ℕ) (which : c.control.Targets) (i : Fin (c.batch.fields*c.placement.shapes)) : Expr :=
  let p:=finProdFinEquiv.symm i
  c.query floor which p.1 p.2

def joinCode (floor w : ℕ) :=
  ROM.mount (DescentResetNodeBooks.page (L).stripWord (L).channels (L).decodedLanes)
    (((L).siteWord+(L).stripWord)*(L).decodedLanes) w (c.tabs floor)
def joinMem (floor : ℕ) (m : Memory w) :=
  ROM.after (DescentResetNodeBooks.page (L).stripWord (L).channels (L).decodedLanes)
    (((L).siteWord+(L).stripWord)*(L).decodedLanes) (c.tabs floor) m
def dictCode (floor w : ℕ) :=ROM.mount (L).wordPages ((L).siteWord*(L).decodedLanes) w (c.lookup floor)
def dictMem (floor : ℕ) (m : Memory w) :=ROM.after (L).wordPages ((L).siteWord*(L).decodedLanes) (c.lookup floor) m

def selected (which : c.control.Targets) (floor : ℕ) (old : Fin (L).sources→Bank) (saved : Bank)
    (packet : Expr) (m : Memory w) :=c.control.image which (c.seen floor) packet ((L).movedImage floor old saved m)
def prepared (which : c.control.Targets) (floor : ℕ) (old : Fin (L).sources→Bank) (saved : Bank)
    (packet : Expr) (m : Memory w) :=c.dictMem floor (c.joinMem floor (c.selected which floor old saved packet m))

def program (floor w : ℕ) (which : c.control.Targets) (keep : Fin c.placement.shapes→Bool)
    (old : Fin (L).sources→Bank) (saved : Bank) (packet : Expr) (cnt inv : Bank) :=
  (((((L).moved floor w old saved).seq (c.control.program which (c.seen floor) w packet)).seq
    (c.joinCode floor w)).seq (c.dictCode floor w)).seq
    (DescentRetainedTargetPlacement.Chart.program c.placement c.batch (c.place floor) w keep (c.terms floor which) cnt inv)
def ticks (floor w : ℕ) (which : c.control.Targets) (old : Fin (L).sources→Bank) (saved : Bank)
    (packet : Expr) (cnt inv : Bank) :=
  ((((L).movedTicks floor w old saved+c.control.ticks which (c.seen floor) w packet)+
    (4+10*((L).channels+1)*2^(((L).siteWord+(L).stripWord)*(L).decodedLanes)))+
    (4+10*(L).outputs*2^((L).siteWord*(L).decodedLanes)))+
    DescentRetainedTargetPlacement.Chart.ticks c.placement c.batch (c.place floor) (c.terms floor which) cnt inv
def image (floor : ℕ) (which : c.control.Targets) (keep : Fin c.placement.shapes→Bool)
    (old : Fin (L).sources→Bank) (saved : Bank) (packet : Expr) (cnt inv : Bank) (m : Memory w):=
  DescentRetainedTargetPlacement.Chart.image c.placement c.batch (c.place floor) keep (c.terms floor which) cnt inv
    (c.prepared which floor old saved packet m)

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
