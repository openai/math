import OAI.Hierarchy.DescentOrdinaryRoleControlPrice

namespace OAI
/-! # The two actual `Measured` population fields after mounting the receiver ROM -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (L : RoleControl.Layout) {w : ℕ}

theorem input_fits (P : Ports L.walks) (old : Fin L.blocks→Bank) (b : Fin L.blocks)
    (access : Accessible P (old b) L.hosts L.groups L.lanes w L.base) {hi}
    (early : L.endAddress≤hi) (room : hi<2^w) (l : Fin L.sites) :
    (L.want P l).Fits w hi ∧ L.counts.Fits w hi := by
  have top : L.outBase≤hi:=(Nat.le_add_right ..).trans early
  have askRoom:=L.bank_fits (early.trans_lt room) (L.askIndex l)
  exact ⟨⟨⟨askRoom.1,askRoom.2.1,askRoom.2.2.trans top⟩,
    ⟨access.chunks.1,access.chunks.2.1,access.chunks.2.2.trans ((Nat.le_add_right ..).trans top)⟩,trivial⟩,
    L.result_fit room early,trivial⟩

theorem measured (P : Ports L.walks) (old : Fin L.blocks→Bank) (b : Fin L.blocks) (m reached : Memory w)
    (order : Fin L.hosts→Fin L.walks→Option (Fin L.hosts))
    (roles : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell (L.roleBits*L.nodes))
    (access : ∀b,Accessible P (old b) L.hosts L.groups L.lanes w L.base)
    (ports : Mounted P (DescentSortedRoster.indexed order) m L.groups L.lanes)
    (previous : ∀b,Reads (old b) (roles b) L.lanes m) (room : L.endAddress<2^w)
    (kept : ∀i,i<L.endAddress → reached i=L.output P old m i) (l : Fin L.sites) :
    Source (L.want P l) (fun (_:Fin L.hosts) (_:Fin L.groups)=>DescentSharedCableNames.Packed.token (some l)) L.lanes reached ∧
    Source L.counts (L.dataCount order roles) L.lanes reached := by
  have controls:=L.issued P old b m order roles access ports previous room
  have fit:=L.input_fits P old b (access b) le_rfl room l
  exact ⟨fun p=>(eval_below _ _ _ _ fit.1 kept).trans (controls.2.2 l p),
    fun p=>(eval_below _ _ _ _ fit.2 kept).trans (controls.2.1 p)⟩

/-- The semantic count includes every live node of the preceding archive,
including a hub equality. It counts no role digit at an unoccupied site. -/
theorem population_at {X : Type} [Fintype X]
    (order : Fin L.hosts→Fin L.walks→Option (Fin L.hosts))
    (roles : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell (L.roleBits*L.nodes))
    (h : Fin L.hosts) (g : Fin L.groups) (walk : Fin L.walks) (block : Fin L.blocks)
    (home : Fin L.hosts) (hit : DescentSortedRoster.indexed order h walk=some home)
    (ids : X↪Fin L.nodes) (ready : ∀j,(encode L.roleBits L.nodes).symm (roles block home g) j≠0 ↔ ∃u,ids u=j)
    (room : L.nodes<2^L.countBits) :
    ((encode L.countBits L.donors).symm (L.dataCount order roles h g) (finProdFinEquiv (walk,block))).val=Fintype.card X := by
  simp only [dataCount,Equiv.symm_apply_apply,RoleCounts.value,hit,Option.elim_some]
  exact RoleCounts.exact_count ids _ ready room

theorem population_absent (order : Fin L.hosts→Fin L.walks→Option (Fin L.hosts))
    (roles : Fin L.blocks→Fin L.hosts→Fin L.groups→Cell (L.roleBits*L.nodes))
    (h : Fin L.hosts) (g : Fin L.groups) (walk : Fin L.walks) (block : Fin L.blocks)
    (miss : DescentSortedRoster.indexed order h walk=none) :
    (encode L.countBits L.donors).symm (L.dataCount order roles h g) (finProdFinEquiv (walk,block))=0 := by
  simp only [dataCount,Equiv.symm_apply_apply,RoleCounts.value,miss,Option.elim_none]

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout

end OAI
