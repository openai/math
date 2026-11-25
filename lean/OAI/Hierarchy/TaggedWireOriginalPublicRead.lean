import OAI.Hierarchy.ProtocolRAMTurnRoleData
import OAI.Hierarchy.TaggedWireOriginalRows
import OAI.Hierarchy.TaggedWireVirtualSites

namespace OAI
/-! # Pointwise native role resolution for every original terminal item -/

noncomputable section
set_option maxHeartbeats 1200000
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM Calendar
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w h W k attempts edges R : ℕ} (S : PurchaseSampler) (L : Chart)

def Socket.view (v : Socket) (m : Memory w) (r : Word w) : Fin 4→Word w :=
  ![v.positive.eval m r,v.ordinal.eval m r,v.group.eval m r,v.slot.eval m r]

theorem resolved_congr (m : Memory w) (a b : Socket) (i j : Word w) (p : Public S h W k attempts)
    (same : a.view m i=b.view m j) (ok : Resolved S L b m j p) : Resolved S L a m i p := by
  let observed (operands : Fin 4→Word w) : Prop :=
    let address := RowOp.add.opcode.eval ((SiteROM.offsets L.offBase L.groups).read m (operands 2)) (operands 3)
    let publicRow := Comparison.eq.test (operands 0) ((0:ℕ):Word w)
    (if publicRow then (RoleROM.bank (L.publicBase+L.publicCount) L.publicCount).read m (operands 1)
      else (SiteROM.sites L.offBase L.groups L.slots).read m address)=((name (site S p)).val:Word w) ∧
    (if publicRow then (RoleROM.bank L.publicBase L.publicCount).read m (operands 1)
      else (RoleROM.bank L.roleBase (L.groups*L.slots)).read m address)=(code S p:Word w)
  change observed (a.view m i)
  rw [same]
  exact ok

theorem branch_view (k : Expr) (n : ℕ) (a b : Socket) (m : Memory w) (i : Word w) :
    (branchSocket k n a b).view m i=if k.eval m i=(n:Word w) then a.view m i else b.view m i := by
  by_cases eq:k.eval m i=(n:Word w) <;> simp [branchSocket,Socket.view,zipSocket,Expr.eval,Comparison.test,eq]

theorem map_view (v : Socket) (index : Expr) (m : Memory w) (i : Word w) :
    (mapSocket (fun e=>e.atRow index) v).view m i=v.view m (index.eval m i) := by simp [mapSocket,Socket.view,eval_atRow]

def roleFor (π : Equiv.Perm (Fin (2^h))) (pay : Fin edges→Bool→PaidPorts S h W k attempts)
    (x : Old h W k edges) (s : Bool) : Public S h W k attempts :=
  publicRoleFor S π (fun e b=>.inl (pay e b)) x s

/-- Only strictly positive physical rows require any bought socket to exist. -/
def activePaid (width : Fin edges→ℕ) (port : ∀e,0<width e→Bool→PaidPorts S h W k attempts)
    (e : Fin edges) (side : Bool) : Public S h W k attempts :=
  if pos:0<width e then .inl (port e pos side) else .inr (.inl (.inl (0,false)))

theorem activePaid_pos (width : Fin edges→ℕ) (port : ∀e,0<width e→Bool→PaidPorts S h W k attempts)
    (e : Fin edges) (positive : 0<width e) (side : Bool) : activePaid S width port e side=.inl (port e positive side) :=
  dite_eq_left positive

theorem original_public (order : Fin R≃Edges S h (2^W) k) (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (metaBase ext axis : ℕ) (core : CatalogueRows.CoreSource) (paid : Bool→Socket)
    (p : Fin edges→Bool→Public S h W k attempts)
    (i : Fin (Fintype.card (Old h W k edges))) (side : Bool)
    (word : ∀j,(«meta» metaBase (Fintype.card (Old h W k edges)) j).eval m (i.val:Word w)=
      (metadataTable S order attempts edges j i:Word w))
    (siteFit : siteLast h (2^W) k+1≤2^w) (wide : 4≤2^w)
    (publicCount : L.publicCount=Fintype.card (Public S h W k attempts)) (countFit : L.publicCount≤2^w)
    (sites : RoleROM.Mounted (L.publicBase+L.publicCount) (publicSites h W k attempts S) m)
    (codes : RoleROM.Mounted L.publicBase (RoleROM.publicTable S h W k attempts) m)
    (paidRows : ∀e,SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) i=.inl e→
      ∀b,Resolved S L (paid b) m (e.val:Word w) (p e b))
    (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w)) (rowsFit : 2^h≤2^w)
    (extTab : ∀s,RoleROM.Mounted (ext+s.toNat*2^h) (exteriorTable h W k attempts S s) m)
    (axisTab : RoleROM.Mounted axis (altTable S h W k attempts) m) (axisFit : (siteLast h (2^W) k+1)*(2*k)≤2^w)
    (readSite : ∀p t l s,(if s then core.right else core.left).eval m ((altRow S order p t l s).val:Word w)=
      ((name (goodsSite (goods π (.inr ((p,t),l),s)) : Site h (2^W) k)).val:Word w)) :
    Resolved S L (originalInputs L metaBase (Fintype.card (Old h W k edges)) ext axis h W k core paid side) m (i.val:Word w)
      (publicRoleFor S π p (SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) i) side) := by
  let n:=Fintype.card (Old h W k edges)
  let pick:=«meta» metaBase n
  let r:Word w:=(i.val:Word w)
  have code_ne {a b:ℕ} (ha:a<4) (hb:b<4) (hne:a≠b) : (a:Word w)≠(b:Word w) := by
    intro eq;apply hne;simpa only [Fin.val_cast_of_lt (ha.trans_le wide),Fin.val_cast_of_lt (hb.trans_le wide)] using congrArg Fin.val eq
  cases old : SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) i with
  | inl e=>
    have tag : (pick 0).eval m r=((0:ℕ):Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 0
    have id : (pick 1).eval m r=(e.val:Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 1
    apply resolved_congr S L m _ (normalized L paid side) r (e.val:Word w) _
    · unfold originalInputs
      rw [branch_view,ite_eq_left tag,map_view,id]
    · exact normalized_site S L paid (p e) m _ (paidRows e old) siteFit side
  | inr x=>
    cases x with
    | inl g=>
      cases g with
      | inl u=>
        have tag : (pick 0).eval m r=((1:ℕ):Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 0
        have id : (pick 1).eval m r=(u.val:Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 1
        apply resolved_congr S L m _ (exterior ext h (pick 1) side) r r _
        · unfold originalInputs
          rw [branch_view,ite_eq_right (fun eq => (code_ne (a:=1) (b:=0) (by decide) (by decide) (by decide)) (tag.symm.trans eq)),branch_view,ite_eq_left tag]
        · exact public_resolved S L _ m r _ rfl publicCount countFit sites codes
            (exterior_ordinal S π ext u _ m r side id rowsFit perm (extTab side))
      | inr v=>
        obtain ⟨⟨u,t⟩,l⟩:=v
        have tag : (pick 0).eval m r=((2:ℕ):Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 0
        have id : (pick (if side then 3 else 2)).eval m r=((altRow S order u t l side).val:Word w) := by
          cases side
          · simpa [pick,r,n,metadataTable,old,metadata] using word 2
          · simpa [pick,r,n,metadataTable,old,metadata] using word 3
        have ax : (pick 4).eval m r=((axisCode l).val:Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 4
        let physical:=altSite core (pick (if side then 3 else 2)) side
        let z:StageColumns h (2^W)×Axis k:=(⟨t,occupiedStagePort π t (u,side)⟩,l)
        have siteAt : physical.eval m r=((altKey z).1.val:Word w) := by
          rw [show physical.eval m r=(if side then core.right else core.left).eval m ((altRow S order u t l side).val:Word w) by
            rw [show physical=altSite core (pick (if side then 3 else 2)) side from rfl,altSite,eval_atRow,id]]
          exact readSite u t l side
        apply resolved_congr S L m _ (altInput axis (siteLast h (2^W) k+1) k physical (pick 4)) r r _
        · unfold originalInputs
          rw [branch_view,ite_eq_right (fun eq => (code_ne (a:=2) (b:=0) (by decide) (by decide) (by decide)) (tag.symm.trans eq)),
            branch_view,ite_eq_right (fun eq => (code_ne (a:=2) (b:=1) (by decide) (by decide) (by decide)) (tag.symm.trans eq)),branch_view,ite_eq_left tag]
        · exact public_resolved S L _ m r _ rfl publicCount countFit sites codes
            (alt_ordinal S axis m r z physical (pick 4) siteAt ax axisTab axisFit)
    | inr c=>
      have tag : (pick 0).eval m r=((3:ℕ):Word w) := by simpa [pick,r,n,metadataTable,old,metadata] using word 0
      have key : (pick (if side then 6 else 5)).eval m r=
          ((Fintype.equivFin (Public S h W k attempts) (.inr (.inr (c,side)))).val:Word w) := by
        cases side
        · simpa [pick,r,n,metadataTable,old,metadata] using word 5
        · simpa [pick,r,n,metadataTable,old,metadata] using word 6
      apply resolved_congr S L m _ (publicInput (pick (if side then 6 else 5))) r r _
      · unfold originalInputs
        rw [branch_view,ite_eq_right (fun eq => (code_ne (a:=3) (b:=0) (by decide) (by decide) (by decide)) (tag.symm.trans eq)),
          branch_view,ite_eq_right (fun eq => (code_ne (a:=3) (b:=1) (by decide) (by decide) (by decide)) (tag.symm.trans eq)),
          branch_view,ite_eq_right (fun eq => (code_ne (a:=3) (b:=2) (by decide) (by decide) (by decide)) (tag.symm.trans eq))]
      · exact public_resolved S L _ m r _ rfl publicCount countFit sites codes key

theorem original_read (order : Fin R≃Edges S h (2^W) k) (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (metaBase ext axis : ℕ) (core : CatalogueRows.CoreSource) (paid : Bool→Socket)
    (p : Fin edges→Bool→PaidPorts S h W k attempts)
    (i : Fin (Fintype.card (Old h W k edges))) (side : Bool)
    (word : ∀j,(«meta» metaBase (Fintype.card (Old h W k edges)) j).eval m (i.val:Word w)=
      (metadataTable S order attempts edges j i:Word w))
    (siteFit : siteLast h (2^W) k+1≤2^w) (wide : 4≤2^w)
    (publicCount : L.publicCount=Fintype.card (Public S h W k attempts)) (countFit : L.publicCount≤2^w)
    (sites : RoleROM.Mounted (L.publicBase+L.publicCount) (publicSites h W k attempts S) m)
    (codes : RoleROM.Mounted L.publicBase (RoleROM.publicTable S h W k attempts) m)
    (paidRows : ∀e,SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) i=.inl e→
      ∀b,Resolved S L (paid b) m (e.val:Word w) (.inl (p e b)))
    (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w)) (rowsFit : 2^h≤2^w)
    (extTab : ∀s,RoleROM.Mounted (ext+s.toNat*2^h) (exteriorTable h W k attempts S s) m)
    (axisTab : RoleROM.Mounted axis (altTable S h W k attempts) m) (axisFit : (siteLast h (2^W) k+1)*(2*k)≤2^w)
    (readSite : ∀p t l s,(if s then core.right else core.left).eval m ((altRow S order p t l s).val:Word w)=
      ((name (goodsSite (goods π (.inr ((p,t),l),s)) : Site h (2^W) k)).val:Word w)) :
    Resolved S L (originalInputs L metaBase (Fintype.card (Old h W k edges)) ext axis h W k core paid side) m (i.val:Word w)
      (roleFor S π p (SettledMatrix.Layout.numbered (r:=edges) (I:=Goods h W k) (A:=Catalysts h W k) i) side) := by
  exact original_public S L order π m metaBase ext axis core paid (fun e b=>.inl (p e b)) i side word
    siteFit wide publicCount countFit sites codes paidRows perm rowsFit extTab axisTab axisFit readSite

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
