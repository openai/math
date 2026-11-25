import OAI.Hierarchy.TaggedWideDatedAddresses
import OAI.Hierarchy.TaggedWirePacketNeighborSlots
import OAI.Hierarchy.TaggedWideRoleMetadata

namespace OAI
/-! # Native neighbor selection from the actual chronological width and opposite-role scatter pages -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe ReportSockets
open WireTelescope Tagged PassiveWindow Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing

variable {h W k attempts n native cap : ℕ} (S : PurchaseSampler)
   (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
   (rows : Fin n≃Source S π depth mark)

theorem named_coordinate (i : Fin n) (b : Bool) :
    (finProdFinEquiv.symm (shelfSlot S (named S π depth mark unique rows (i,b)))).1 =
      (portGraph (siteLast h (2^W) k+1)).vertex ((sorted S π depth mark ∘ rows) i) b := by
  let p := named S π depth mark unique rows (i,b)
  change (finProdFinEquiv.symm (finProdFinEquiv
    (name (site S p), (⟨code S p,code_bound S p⟩ : Fin (stride k S.degree attempts))))).1 = _
  rw [Equiv.symm_apply_apply]
  exact named_site S π depth mark unique rows i b

variable (qty : Fin n→ℕ) (s : Fin (siteLast h (2^W) k+1)) (bounded : ∀i,qty i≤cap)
    {total : Widths (siteLast h (2^W) k+1)} (shape : installedWidths (sorted S π depth mark ∘ rows) qty=total)

theorem page_read {c d : ℕ} (page stride : Bank) (expr : Expr) (m : Memory native) (r : Word native)
    (s : Fin c) (q : Fin d) (atSite : stride.read m (expr.eval m r)=((s.val*d : ℕ):Word native))
    (fits : c*d≤2^native) (cap : c*d≤page.size) :
    (pageRead page stride expr q).eval m r=m (page.base+(finProdFinEquiv (s,q)).val) := by
  have addr : (finProdFinEquiv (s,q)).val=s.val*d+q.val := by
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have nfit : s.val*d+q.val<2^native:=addr ▸ (finProdFinEquiv (s,q)).isLt.trans_le fits
  have pfit : s.val*d+q.val<page.size:=addr ▸ (finProdFinEquiv (s,q)).isLt.trans_le cap
  rw [pageRead,Expr.eval,RoleWidths.offset_at stride expr (.lit q.val) m r s.val q.val d atSite rfl,
    Bank.read,Fin.val_cast_of_lt nfit,Nat.mod_eq_of_lt pfit,addr]

/-- Both public operands use the actual positive (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S) in the original
distributed role table. Every numerical hole reads width zero. This works
even when the named role's partner site has numerical index zero. -/
theorem metadata_neighbors (widthPage oppositePage baseAt : Bank) (siteWord : Expr) (m : Memory native)
    (row : Word native) (one : 1<2^native) (rowFits : ∀i,qty i<2^native)
    (space : (siteLast h (2^W) k+1)*stride k S.degree attempts≤2^native)
    (widthRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤widthPage.size)
    (oppositeRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤oppositePage.size)
    (atSite : baseAt.read m (siteWord.eval m row)=((s.val*(stride k S.degree attempts) : ℕ):Word native))
    (widthRead : ∀t : Fin ((siteLast h (2^W) k+1)*(stride k S.degree attempts)),m (widthPage.base+t.val)=
      (RoleWidths.shelf (named S π depth mark unique rows)
        (shelfSlot S) (fun z=>qty z.1) t : Word native))
    (otherRead : ∀t : Fin ((siteLast h (2^W) k+1)*(stride k S.degree attempts)),m (oppositePage.base+t.val)=
      (RoleWidths.shelf (named S π depth mark unique rows)
        (shelfSlot S) (RoleField.data .opposite (fun z : Fin n×Bool=>qty z.1) (fun _=>0)
          (fun z : Fin n×Bool=>(name (site S (named S π depth mark unique rows (z.1,!z.2)))).val)) t : Word native)) :
    PacketTurns.NeighborReads m row
      (carried (sorted S π depth mark ∘ rows) qty s bounded
        (PacketNeighbor.localSlot (sorted S π depth mark ∘ rows) qty
          (named S π depth mark unique rows) (shelfSlot S) (named_coordinate S π depth mark unique rows) s) shape)
      (pageRead widthPage baseAt siteWord) (pageRead oppositePage baseAt siteWord) := by
  let ends := sorted S π depth mark ∘ rows
  let port := named S π depth mark unique rows
  let slot := shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S
  let here := named_coordinate S π depth mark unique rows
  let seat := PacketNeighbor.localSlot ends qty port slot here s
  let opposite := RoleField.data .opposite (fun z : Fin n×Bool=>qty z.1) (fun _=>0)
    (fun z : Fin n×Bool=>(name (site S (port (z.1,!z.2)))).val)
  refine ⟨one,?_,?_,?_⟩
  · intro q
    by_cases hit:∃a,seat a=q
    · obtain ⟨a,rfl⟩:=hit
      rw [PacketNeighbor.amount,PacketNeighbor.local_owner,Option.elim_some,PacketNeighbor.local_width]
      exact rowFits _
    · rw [PacketNeighbor.amount,PacketNeighbor.local_blank ends qty port slot here s bounded shape q hit,Option.elim_none]
      exact Nat.two_pow_pos _
  · intro q
    rw [page_read widthPage baseAt siteWord m row s q atSite space widthRoom,widthRead,
      PacketNeighbor.width_at ends qty port slot here s bounded shape q]
  · intro q p own live
    rw [page_read oppositePage baseAt siteWord m row s q atSite space oppositeRoom,otherRead]
    apply congrArg (fun a : ℕ=>(a : Word native))
    apply PacketNeighbor.other_at ends qty port slot here s bounded shape q p own opposite
    intro i b positive
    simpa [opposite,port,ends,RoleField.data,positive.ne'] using congrArg Fin.val (named_site S π depth mark unique rows i (!b))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
