import OAI.Hierarchy.DescentOrdinaryOriginPorts
import OAI.Hierarchy.DescentDatedRoutedArguments

namespace OAI
/-! # The ordinary resolver's dated actor-origin bank and six native field lookups -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open DescentSIMDLookup DescentHaloWalkRAM DescentPackedActorMask DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def originCandidates :=nodes (breadth v.reference.degree*2^v.reference.k) v.reference.oldNodes v.reference.capacity
def originBits :=Nat.clog 2 (v.originCandidates+1)

theorem originBits_fit : v.originCandidates<2^v.originBits:=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)

def originChart : Return :=
  ⟨v.reference.degree,v.reference.k,v.reference.oldNodes,v.reference.capacity,v.resolver.nodes,v.originBits,
    v.vector.hosts,v.vector.lows,v.vector.groups,v.vector.radix,v.vector.lanes⟩
def originPortFloor (floor : ℕ) :=v.originChart.finish (v.routedStart floor)
def originPortEnd (floor : ℕ):=DescentOrdinaryOriginPorts.endAddress v.originChart (v.originPortFloor floor)
def originControlWords:=v.originChart.preparationWords+words v.originChart

theorem originPort_span (floor : ℕ) : v.originPortEnd floor=v.routedStart floor+v.originControlWords:=by
  simp only [originPortEnd,DescentOrdinaryOriginPorts.endAddress,originPortFloor,Return.affine,originControlWords,Nat.add_assoc]

def originBank (floor : ℕ) (block : Fin v.vector.radix) :=v.originChart.returned (v.routedStart floor) block
def originPort (floor outBits : ℕ) (block : Fin v.vector.radix) (node : Fin v.resolver.nodes) (field : Fin 6) :=
  DescentOrdinaryOriginPorts.expr v.originChart outBits (v.routedStart floor) (v.originPortFloor floor) block node field

def originPrefix (floor outBits w : ℕ)
    (C : Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity) : NativePhase w :=
  let base:=v.originPortFloor floor
  let maskPhase:=v.originChart.phase C (v.routedStart floor) w
  maskPhase.seq ⟨DescentOrdinaryOriginPorts.program v.originChart outBits base w,4+10*words v.originChart,
    DescentOrdinaryOriginPorts.image v.originChart outBits base,DescentStaticWordColumn.cheap w base _ _⟩

theorem originPrefix_run (floor outBits w : ℕ) (C : Fin v.vector.lows→Refs v.reference.degree v.reference.k
    v.reference.oldNodes v.reference.capacity) (m : Memory w)
    (fit : ∀l,(mask (C l)).Fits w (v.routedStart floor)) (space : v.originPortEnd floor<2^w) :
    (v.originPrefix floor outBits w C).Runs m ∧
      ∀t,t<v.routedStart floor ∨ v.originPortEnd floor≤t → (v.originPrefix floor outBits w C).image m t=m t:=by
  have between : v.routedStart floor≤v.originPortFloor floor:=by rw [originPortFloor,Return.affine];omega
  have below : v.originPortFloor floor≤v.originPortEnd floor:=Nat.le_add_right ..
  have first:=v.originChart.framed C (v.routedStart floor) m fit (below.trans_lt space)
  have later:=DescentOperandFamilyBook.any (DescentOrdinaryOriginPorts.law v.originChart outBits)
    v.vector.lanes (v.originPortFloor floor) (v.originChart.image C (v.routedStart floor) m) space
  refine ⟨Procedure.Exec.then first.1 later.1,?_⟩
  intro t out
  exact (later.2.2.1 t (out.imp_left (fun h=>h.trans_le between))).trans
    (first.2.2 t (out.imp_right (fun h=>below.trans h)))

/-- The six resolver expressions read the W result in the actual two-stage
program image, through the positively issued original actor selectors. -/
theorem originPrefix_ports {a nb mb} (floor outBits w : ℕ)
    (C : Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity)
    (V : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb) (m : Memory w)
    (hm : 0<v.vector.lanes) (hr : 0<v.vector.radix)
    (measured : ∀i,Measured (C i) (V i) v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.routedStart floor) m)
    (space : v.originPortEnd floor<2^w) (x : Fin v.vector.radix) (node : Fin v.resolver.nodes) (f : Fin 6) :
    let data_:=DescentScalarBookReshape.book
      (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits (marked (V l) h g)) x
    (v.originPort floor outBits x node f).Fits w (v.originPortEnd floor) ∧
      Source (v.originPort floor outBits x node f) (fun h g=>readLaw v.originChart outBits node f (data_ h g)) v.vector.lanes
        ((v.originPrefix floor outBits w C).image m):=by
  intro data_
  have fit : v.originPortFloor floor<2^w:=(Nat.le_add_right _ _).trans_lt space
  have source:=v.originChart.originReturned C (v.routedStart floor) m hm hr V measured fit x
  have adr:=v.originChart.grid.returned_fits (v.originChart.rowsAt (v.routedStart floor)) x fit
  exact DescentOrdinaryOriginPorts.issued v.originChart outBits _ _ _ x node f data_ adr.1 adr.2 source space


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
