import OAI.Hierarchy.DescentAcquiredRolePage

namespace OAI
/-! Exact role words beyond the old archive host shelf, using the original site's placement. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentCompiler DescentKernelHistory DescentPrimitivePalette
open DescentLocalArchiveOrder DescentSIMDLookup DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {clock : AtomSchedule} {k i z D wire hist s Z : ℕ}
  (r : Reached W G q ε clock k i z D wire hist) (arch : BitDescription W) (number : Local arch)
  (ports : DatePorts) (room : RangeRoom ports r arch) (op : RotorSpec)
  (labels : NodeOrder.All arch→Label G s Z op)

theorem acquired_sparse_role_page {H width : ℕ}
    (wide : Fintype.card r.V≤H)
    (roles : Block k→Fin ports.operandHosts→Fin ports.venue.groups→Cell (width*ports.nodes))
    (published : ∀b h g,(roles b h g).val=(encode (printedBits G s Z op) ports.nodes (fun n=>
      (slotAt ports r arch number room (b.cast (congrArg (2^·) room.radix)) n h g).elim 0
        (fun y=>token G s Z op (labels y)))).val)
    (b : Block k) (h : Fin (Fintype.card r.V)) (g : Fin (clock.groupCount i)) :
    (DescentOrdinaryHostPad.extend H (roles b) (h.castLE wide) (g.cast room.groups)).val=
      (Reached.NodeCells.rolePage (N:=ports.nodes) r arch number (fun y=>token G s Z op (labels y)) b h g).val:=by
  by_cases inside:(h.castLE wide).val<ports.operandHosts
  · rw [DescentOrdinaryHostPad.extend,dite_eq_left inside,published]
    simp only [Reached.NodeCells.rolePage,slot_at_host]
    rfl
  · rw [DescentOrdinaryHostPad.extend,dite_eq_right inside]
    have blank(j:Fin ports.nodes):Reached.NodeCells.atPhysical r arch number b j h g=none:=by
      cases hit:Reached.NodeCells.atPhysical r arch number b j h g with
      | none=>rfl
      | some v=>
        have point:=(Reached.NodeCells.atPhysical_some r arch number b j h g v.1 v.2).mp hit
        have fits:=(room.hosts v.1)
        change (r.vertex (r.placement.pos v.1).2).val<ports.operandHosts at fits
        exact False.elim (inside (point.1 ▸ fits))
    simp only [Reached.NodeCells.rolePage,blank,Option.elim_none]
    change 0=(finFunctionFinEquiv (fun _:Fin ports.nodes=>(0:Cell (printedBits G s Z op)))).val
    simp []

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
