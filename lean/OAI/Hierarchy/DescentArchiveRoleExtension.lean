import OAI.Hierarchy.DescentDatePortArchiveRead
import OAI.Hierarchy.DescentOrdinaryHostPad

namespace OAI
/-! The role input of an ordinary step has the original node order after changing
the previous physical host extent. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}


open DescentOrdinaryHostPad
local notation "slot" => slotAt ports r B number room
local notation "tok" => token G s Z op
local notation "bits_" => printedBits G s Z op

theorem extended_roles (H : ℕ) (x : Fin (2^ports.venue.k)) (h : Fin H) (g : Fin ports.venue.groups) :
    extend H (fun v t=>encode bits_ ports.nodes (fun j=>(slot x j v t).elim 0 (fun y=>tok (label y)))) h g =
      Reached.NodeCells.rolePage (N:=ports.nodes) r B number (fun y=>tok (label y))
        (x.cast (congrArg (2^·) room.radix.symm)) h (g.cast room.groups.symm):=by
  let b:=x.cast (congrArg (2^·) room.radix.symm)
  let group:=g.cast room.groups.symm
  by_cases fits:h.val<ports.operandHosts
  · rw [extend,dite_eq_left fits]
    rfl
  · rw [extend,dite_eq_right fits]
    have hole (j : Fin ports.nodes) : Reached.NodeCells.atPhysical r B number b j h group=none:=by
      cases hit:Reached.NodeCells.atPhysical r B number b j h group with
      | none=>rfl
      | some node=>
        obtain ⟨site,node⟩:=node
        have atHost:=(Reached.NodeCells.atPhysical_some r B number b j h group site node).mp hit
        have hw : (r.vertex (r.placement.pos site).2).val<ports.operandHosts:=room.hosts site
        exact False.elim (fits (atHost.1 ▸ hw))
    symm
    apply Fin.ext
    change (finFunctionFinEquiv (fun j : Fin ports.nodes=>
      (Reached.NodeCells.atPhysical r B number b j h group).elim (0:Cell bits_) (fun y=>tok (label y)))).val=0
    simp [hole]

/-- Read the archived primitive token of an actual original node at the padded receiver. -/
theorem extended_role_node {H : ℕ} (name : r.V↪Fin H) (faith : ∀v,(name v).val=(r.vertex v).val)
    (v : W.graph.Site) (n : (B.recipe v).Node) (j : Fin ports.nodes) (ordinal : j.val=(number v n).val) :
    let x:=(r.placement.block v).cast (congrArg (2^·) room.radix)
    let g:=(r.placement.pos v).1.cast room.groups
    (encode bits_ ports.nodes).symm (extend H (fun h g=>encode bits_ ports.nodes
      (fun t=>(slot x t h g).elim 0 (fun a=>tok (label a)))) (name (r.placement.pos v).2) g) j =
      tok (label ⟨v,n⟩):=by
  intro x g
  rw [extended_roles]
  simpa [x,g] using Reached.NodeCells.role_at r B number name faith (fun a=>tok (label a)) v n j ordinal

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
