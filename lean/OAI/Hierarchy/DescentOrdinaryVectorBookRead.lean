import OAI.Hierarchy.DescentOrdinaryGatherOnly
import OAI.Hierarchy.DescentOrdinaryMeasureCut
import OAI.Hierarchy.DescentDatedOperandBanks

namespace OAI
/-! Read the node array on every real gathered argument page, including its padding. -/
namespace Hierarchy.DescentOperandVectorArena.References
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSIMDLookup DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
variable {D k K cap width nb mb w : ℕ} (A : Layout) (C : References A D k K cap)
abbrev Rows (A : Layout) (D k K cap width nb mb : ℕ) :=
  Fin A.pageCount→Fin A.lows→Values D k K cap A.hosts (A.groups*A.radix) width nb mb

def returnedValue (V : Rows A D k K cap width nb mb) (next : ℕ) (page : Fin A.pageCount) (b : Fin A.radix) :=
  DescentScalarBookReshape.book (fun q h g=>(V page q).book next h g) b

theorem reads (V : Rows A D k K cap width nb mb) (next start : ℕ) (m : Memory w)
    (bits : A.bookBits=width*next) (hm : 0<A.lanes) (hr : 0<A.radix)
    (measured : ∀p q,Measured (C p q) (V p q) next (A.lanes*A.radix) start m)
    (room : A.endAddress start<2^w) :
    ∀p b,Reads (DescentVectorBookReshape.blockBank (A.out start) A.hosts A.lows A.groups A.radix A.lanes p b)
      (returnedValue A V next p b) A.lanes ((C.phase w start).image m) :=by
  cases A with
  | mk ops normalized state H Q J radix lanes bookBits =>
    change bookBits=width*next at bits
    subst bookBits
    let A : Layout:=⟨ops,normalized,state,H,Q,J,radix,lanes,width*next⟩
    have raised : start≤(A.scratch start).base:=by dsimp only [Layout.scratch,Layout.norm];omega
    have got:=DescentGatheredVectorReshape.run C V (A.tables start) (A.out start) next (A.scratch start) m
      hm hr rfl id (fun _=>rfl) (fun p q=>(measured p q).later_cut raised) (arranged A start room)
    exact fun p b row=>got.2.1 p b row

end
end Hierarchy.DescentOperandVectorArena.References

namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandVectorArena DescentOperandStateBanks DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ} (l : Layout) (A : DescentOperandVectorArena.Layout)
def previousValues (op : l.operands=A.operands) (blocks : l.blocks=A.radix) (hosts : l.hosts=A.hosts*A.lows)
    (groups : l.groups=A.groups) {u : ℕ}
    (value : Fin A.pageCount→Fin A.radix→Fin (A.hosts*A.lows)→Fin A.groups→Cell u)
    (p : Pages l.operands) (x : Fin l.blocks) (h : Fin l.hosts) (g : Fin l.groups) :=
  value (p.cast (congrArg (7*·) op)) (x.cast blocks) (h.cast hosts) (g.cast groups)

theorem previous_values_read (op : l.operands=A.operands) (blocks : l.blocks=A.radix) (hosts : l.hosts=A.hosts*A.lows)
    (groups : l.groups=A.groups) (lanes : l.lanes=A.lanes) {u : ℕ}
    (value : Fin A.pageCount→Fin A.radix→Fin (A.hosts*A.lows)→Fin A.groups→Cell u) (start : ℕ)
    (m : Memory w) (physical : ∀p b,Reads
      (DescentVectorBookReshape.blockBank (A.out start) A.hosts A.lows A.groups A.radix A.lanes p b)
      (value p b) A.lanes m) :
    ∀p x,Reads (previousBank l (A.out start) x p) (previousValues l A op blocks hosts groups value p x) l.lanes m :=by
  cases l with
  | mk oldBlocks nodes oldOperands oldHosts oldGroups oldLanes size =>
    cases A with
    | mk operands normalized state hostCount lowCount groupCount radix laneCount bits =>
      change oldOperands=operands at op
      change oldBlocks=radix at blocks
      change oldHosts=hostCount*lowCount at hosts
      change oldGroups=groupCount at groups
      change oldLanes=laneCount at lanes
      subst oldOperands
      subst oldBlocks
      subst oldHosts
      subst oldGroups
      subst oldLanes
      exact fun p x => physical p x

end
end Hierarchy.DescentDatedPriorOperand

end OAI
