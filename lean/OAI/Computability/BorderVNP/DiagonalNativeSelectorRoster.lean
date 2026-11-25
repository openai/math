import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows
import OAI.Computability.BorderVNP.RoutingISACellBankPhysical
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally

/-! # The selector-dependent physical owner of each joined signed cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM BorderVNP.Cube Physical Evaluator.PositiveTeam

variable {dim blocks b h K s w : ℕ} {A : Type*} [Fintype A]
    {g : GroupWeights.Layout} {teams : TeamNative.Layout} {banks : CellBanks.Layout}
    {orig scheduled : ℕ → ℕ} {decl : LengthDeclaration dim g.groups}
    (select : Packet dim g.groups blocks → Selector dim K h) (pass : passesLengths b s select decl)
    (label : Fin g.cells → Label (dim+1) g.groups) (recv : A → Fin g.cells) (dataWidth : A → ℕ)
    (layout : CellBanks.ScheduleLayout banks g teams) (res : GroupWeights.ScheduleResult g teams orig scheduled)
    (image : GroupWeights.PhysicalImage g orig blocks b K h decl label recv dataWidth)

include pass layout res image

/-- The installed owner column of the cell bank selects the group named by the
passing selector declaration, then reads that group's true greedy team. -/
theorem selected_cell_owner (c : Fin g.cells) :
    banks.written scheduled banks.cells (banks.dest+2*c.val) =
      (greedyOwner teams.r b s label recv dataWidth select (label c (chosen b s select))).val := by
  have axis := congrArg Prod.fst ((passesLengths_iff b s select decl).mp pass)
  change decl.1=chosen b s select at axis
  have stored := (banks.written_at scheduled (show c.val < banks.cells from layout.cells.symm ▸ c.isLt)).1
  have actual := layout.cell_owner res image c
  have group := res.owners _ (label c decl.1).isLt
  have greedy := greedyOwner_stored res select pass label recv dataWidth image (label c decl.1)
  rw [←axis]
  exact stored.trans (actual.trans (group.symm.trans greedy))

/-- A genuine native task roster reading the installed bank has the actual selected
owner at every global ordinal. This uses only the ownership words in the two-word
bank array before the task builder, so arbitrary bottom report bits are permitted. -/
theorem OwnerTable.from_selected_bank {pub : Arg → Word w} {m : Memory w} (l : TypedTaskBuilder.Layout)
    (src : ℕ → ℕ) (team base : ℕ) (id : l.team=team) (baseEq : l.calls=base) (count : l.cells=g.cells)
    (bankBase : l.banks=banks.dest)
    (kept : ∀ c : Fin g.cells, src (banks.dest+2*c.val)=banks.written scheduled banks.cells (banks.dest+2*c.val))
    (old : OwnerTable pub m ⟨l.team,l.calls,l.cells⟩ (l.owner src)) :
    OwnerTable pub m ⟨team,base,g.cells⟩
      (ownerWord (fun c => greedyOwner teams.r b s label recv dataWidth select (label c (chosen b s select)))) := by
  refine ⟨old.frame.trans (by rw [id,baseEq,count]),?_⟩
  intro i hi
  let c : Fin g.cells := ⟨i,hi⟩
  have word := old.atRow i (show i < l.cells by rw [count]; exact hi)
  change readings m (i*3+l.calls)=src (l.banks+2*i) at word
  change readings m (i*3+base)=_
  rw [←baseEq,word,bankBase,kept c,ownerWord,dite_eq_left hi]
  exact selected_cell_owner select pass label recv dataWidth layout res image c

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
