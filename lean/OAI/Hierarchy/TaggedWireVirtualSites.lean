import OAI.Hierarchy.TaggedWireOriginalSocketExpr
import OAI.Hierarchy.TaggedWireOriginalTableData
import OAI.Hierarchy.ProtocolRAMCoreCatalogueRows
import OAI.Hierarchy.TaggedWireHistorySockets

namespace OAI
/-! # Native operand constructors for initial payload, held altimeter, and reserve legs -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {w h W k R H attempts : ℕ} (S : PurchaseSampler)
theorem alt_index (q : StageColumns h (2^W)×Axis k) :
    altTable S h W k attempts (finProdFinEquiv ((altKey q).1,axisCode q.2)) =
      (Fintype.equivFin (Public S h W k attempts) (.inr (.inl (.inr q)))).val := by
  have present : ∃u,altKey u=((altKey q).1,q.2) := ⟨q,rfl⟩
  have decode : (Fintype.equivFin (Axis k)).symm
      (Fin.cast (by simp [Axis,Nat.mul_comm]) (axisCode q.2))=q.2 := by
    apply (Fintype.equivFin (Axis k)).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext rfl
  unfold altTable
  rw [Equiv.symm_apply_apply]
  dsimp only
  rw [decode]
  rw [dite_eq_left present]
  have picked : present.choose=q := altKey_injective (show altKey present.choose=altKey q from present.choose_spec)
  exact congrArg (fun z : StageColumns h (2^W)×Axis k =>
    (Fintype.equivFin (Public S h W k attempts) (.inr (.inl (.inr z)))).val) picked

theorem alt_ordinal (base : ℕ) (m : Memory w) (r : Word w) (x : StageColumns h (2^W)×Axis k)
    (a l : Expr) (siteAt : a.eval m r=((altKey x).1.val:Word w)) (axisAt : l.eval m r=((axisCode x.2).val:Word w))
    (table : RoleROM.Mounted base (altTable S h W k attempts) m) (room : (siteLast h (2^W) k+1)*(2*k)≤2^w) :
    (altInput base (siteLast h (2^W) k+1) k a l).ordinal.eval m r=
      ((Fintype.equivFin (Public S h W k attempts) (.inr (.inl (.inr x)))).val:Word w) := by
  have addr : (Expr.op .add (scale (2*k) a) l).eval m r=
      ((finProdFinEquiv ((altKey x).1,axisCode x.2)).val:Word w) := by
    simp only [Expr.eval,RowOp.opcode,BinaryOp.eval,eval_scale,axisAt,siteAt,←Nat.cast_mul,←Nat.cast_add]
    apply congrArg (fun n:ℕ=>(n:Word w))
    change (2*k)*(altKey x).1.val+(axisCode x.2).val=(axisCode x.2).val+(2*k)*(altKey x).1.val
    exact Nat.add_comm ..
  exact (RoleROM.read table _ r _ room addr).trans (congrArg (fun n:ℕ=>(n:Word w)) (alt_index S x))

theorem exterior_ordinal (π : Equiv.Perm (Fin (2^h))) (base : ℕ) (p : Fin (2^h)) (word : Expr) (m : Memory w)
    (r : Word w) (side : Bool) (seen : word.eval m r=(p.val:Word w)) (room : 2^h≤2^w)
    (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w))
    (table : RoleROM.Mounted (base+side.toNat*2^h) (exteriorTable h W k attempts S side) m) :
    (exterior base h word side).ordinal.eval m r=
      ((Fintype.equivFin (Public S h W k attempts) (.inr (.inl (goods π (.inl p,side))))).val:Word w) := by
  cases side with
  | false=>exact RoleROM.read table word r p room seen
  | true=>
    have target : (Expr.lookup ⟨0,h⟩ word).eval m r=((π p).val:Word w) := by
      simp only [Expr.eval,Bank.read,seen,Fin.val_cast_of_lt (p.isLt.trans_le room),Bank.size,
        Nat.mod_eq_of_lt p.isLt,Nat.zero_add,perm]
    exact RoleROM.read table _ r (π p) room target

theorem alt_site (c : CatalogueRows.CoreSource) (order : Fin R≃Edges S h (2^W) k) (M : ℕ)
    (dir : TaggedShorterSupergroups.Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (read : CoreCatalogue.Rows c order dir π M m)
    (p : Fin (2^h)) (t : StageAt h (2^W)) (l : Axis k) (side : Bool) (index : Expr) (r : Word w)
    (slot : index.eval m r=((altRow S order p t l side).val:Word w)) :
    (altSite c index side).eval m r=
      ((name (goodsSite (goods π (.inr ((p,t),l),side)) : Site h (2^W) k)).val:Word w) := by
  have entries:=read (altRow S order p t l side)
  cases side
  · rw [altSite,eval_atRow,slot]
    refine entries.2.1.trans ?_
    change _=((name (goodsSite (.inr (⟨t,occupiedStagePort π t (p,false)⟩,l)) : Site h (2^W) k)).val:Word w)
    rw [occupiedStagePort_in]
    simp only [altRow,Equiv.apply_symm_apply]; rfl
  · rw [altSite,eval_atRow,slot]
    refine entries.2.2.1.trans ?_
    change _=((name (goodsSite (.inr (⟨t,occupiedStagePort π t (p,true)⟩,l)) : Site h (2^W) k)).val:Word w)
    rw [occupiedStagePort_out]
    simp only [altRow,Equiv.apply_symm_apply]; rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
