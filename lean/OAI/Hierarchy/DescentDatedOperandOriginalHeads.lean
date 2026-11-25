import OAI.Hierarchy.DescentDatedOperandRootSize
import OAI.Hierarchy.DescentDatedOperandPageSockets
import OAI.Hierarchy.DescentDatedLocalRankPages
import OAI.Hierarchy.DescentDatedOriginMouth
import OAI.Hierarchy.DescentDatedWOrigin
import OAI.Hierarchy.DescentDatedOldHeaderProgram
import OAI.Hierarchy.DescentDatedMaterialSockets
import OAI.Hierarchy.DescentDatedRoutedArguments

namespace OAI
/-! # Original bank addresses of the preceding actor, matched seat and newborn mouth -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentSIMDLookup DescentHaloWalkRAM DescentDatedAddressBook
open DescentPackedColony DescentSharedCableNames DescentOrdinaryAtomFieldRAM DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "P" => breadth (fmt).degree
local notation "b" => (e).fieldBits
local notation "M" => (e).lanes
local notation "G" => (e).groups
local notation "H" => (e).oldHosts
local notation "B" => (e).blocks
local notation "l" => v.resolver

def operandPathStart (floor : ℕ) :=
  DescentDatedOperandPages.lastAddress fmt v.operandDepotLayout (v.originMouthEnd floor)
def operandRankStart (floor : ℕ) :=
  DescentDatedSourcePathDirectory.stop (v.operandPathStart floor) H G M (fmt).degree
def operandOldHeaderStart (floor : ℕ) :=DescentDatedSourcePathDirectory.Local.stop (v.operandRankStart floor) H (fmt).degree
def operandMouthHeaderStart (floor : ℕ) :=v.operandOldHeaderStart floor+(l).nodes*2^((((l).size+2)*(l).nodes)*(l).lanes)
def operandHeaderEnd (floor : ℕ) :=v.operandMouthHeaderStart floor+(l).nodes*2^((v.bornBook.bits*(l).nodes)*(l).lanes)

def operandDepot (floor w : ℕ) (A : v.ArgumentEntry) :=
  DescentDatedOperandPages.phase fmt v.operandDepotLayout (v.originMouthEnd floor) w A.venue.panel
def operandPaths (floor w : ℕ) :=
  let inputs:=DescentDatedSourcePathDirectory.nativeBanks H G M (fmt).degree (v.donorEnd floor)
  DescentDatedSourcePathDirectory.allPages inputs (v.operandPathStart floor) H G M (fmt).degree w

def operandRankPhase (floor w : ℕ) :=
  let rankInputs:=PriorHeader.rankBanks H G M (fmt).degree (v.donorEnd floor)
  (DescentDatedSourcePathDirectory.Local.job rankInputs H (fmt).degree).atBase (v.operandRankStart floor) w

def previousHeaderPhase (a n lanes base w : ℕ) : NativePhase w :=
  ⟨DescentOrdinaryAtomFieldRAM.ROM.mount (ScalarOperand.pages a n lanes) ((a*n)*lanes) w base,
    4+10*(n*2^((a*n)*lanes)),DescentOrdinaryAtomFieldRAM.ROM.after (ScalarOperand.pages a n lanes) ((a*n)*lanes) base,
    DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _⟩

def operandHeaderPhase (floor w : ℕ) :=
  (previousHeaderPhase ((l).size+2) (l).nodes (l).lanes (v.operandOldHeaderStart floor) w).seq
    (previousHeaderPhase v.bornBook.bits (l).nodes (l).lanes (v.operandMouthHeaderStart floor) w)
def operandEarlyPhase (floor w : ℕ) (A : v.ArgumentEntry) :=
  (((v.operandDepot floor w A).seq (v.operandPaths floor w)).seq (v.operandRankPhase floor w)).seq (v.operandHeaderPhase floor w)

def oldHeaderAt (floor : ℕ) (job : Fin (l).jobs) (f : Fin 4) : Expr :=
  let (block,node,arg):=(l).index.symm job
  let bank:=(v.nativeArgs floor).previous block (page (f.castLE (by decide : 4≤7)) arg)
  ScalarOperand.headerExpr (v.operandOldHeaderStart floor) ((l).size+2) (l).nodes (l).lanes bank node

def originAt (floor a : ℕ) (shape : v.VectorShape) (job : Fin (l).jobs) (f : Fin 6) : Expr :=
  let (block,node,_):=(l).index.symm job
  v.originPort floor a (block.cast shape.blocks) node f

def mouthAt (floor : ℕ) (A : v.ArgumentEntry) (match_ : A.Match v floor) (shape : v.VectorShape)
    (job : Fin (l).jobs) (f : Fin 3) : Expr :=
  let (block,node,arg):=(l).index.symm job
  let bank:=v.originMouthBank floor match_.newBlocks (arg.cast (shape.operands.trans match_.newArgs.symm)) f (block.cast shape.blocks)
  ScalarOperand.headerExpr (v.operandMouthHeaderStart floor) v.bornBook.bits (l).nodes (l).lanes bank node

def operandRanks (floor : ℕ) :=PriorHeader.rankBanks H G M (fmt).degree (v.donorEnd floor)
def operandRoster (floor : ℕ) :=PriorHeader.ports H G M (fmt).degree (v.donorEnd floor)
def operandDatum (floor : ℕ) (jobBlock : Fin B) (path : Fin P) (col : Fin (DescentDatedOperandPages.count fmt)) : Expr :=
  DescentDatedOperandPages.socket fmt H G (e).hosts M B b ((e).projectionStart (v.materialStart floor))
    (v.operandRanks floor) (v.operandRoster floor)
    (DescentDatedOperandPages.resultBank fmt v.operandDepotLayout (v.originMouthEnd floor) col) path jobBlock

/-- The public successor block fixes the low *group* of the earlier bank. The
independently selected previous block inside the donor word comes from W. -/
def oldSlotHead (floor : ℕ) (jobBlock : Fin B) (j : Fin 4)
    (i : Fin (P*((fmt).blocks*((fmt).degree*(fmt).cap)))) : Expr :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,s):=finProdFinEquiv.symm t
  let (peer,first):=finProdFinEquiv.symm s
  v.operandDatum floor jobBlock p (DescentDatedOperandPages.header fmt x peer first j)

def anchorHead (floor : ℕ) (jobBlock : Fin B) (j : Fin 5)
    (i : Fin (P*((fmt).blocks*((fmt).cap*3)))) : Expr :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,s):=finProdFinEquiv.symm t
  let (old,mode):=finProdFinEquiv.symm s
  let col:=if live : mode.val<2 then DescentDatedOperandPages.anchor fmt x old ⟨mode.val,live⟩ j
    else DescentDatedOperandPages.sibling fmt x old j
  v.operandDatum floor jobBlock p col

def receiverMap (floor : ℕ) :=
  DepotRAM.Material.Route.bank (e).hosts G M (DepotRAM.Material.Route.Projection.mapBase b B M
    ((e).projectionStart (v.materialStart floor)))
def previousPathHead (floor : ℕ) (i : Fin (P*((fmt).degree+1))) : Expr :=
  let (p,d):=finProdFinEquiv.symm i
  let hdr:=DescentDatedSourcePathDirectory.chart (v.operandPathStart floor) H G M p d
  DepotRAM.Material.Route.lift (v.receiverMap floor) (H*chunks G M) (DescentSharedLeafLookup.source hdr (0:Fin 1))

def rawFieldHead (floor : ℕ) (jobBlock : Fin B) (j : Fin 6) (i : Fin (P*DepotRAM.Material.roles fmt)) : Expr :=
  let (p,lo):=finProdFinEquiv.symm i
  v.rawSocket (v.materialStart floor) (v.operandRanks floor) (v.operandRoster floor) p
    ((DepotRAM.Material.seatIndex fmt).symm lo) jobBlock j

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
