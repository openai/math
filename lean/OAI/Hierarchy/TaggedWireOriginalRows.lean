import OAI.Hierarchy.TaggedWireOriginalSocketExpr
import OAI.Hierarchy.TaggedWireOriginalTableData
import OAI.Hierarchy.TaggedWireRoleSemantics

namespace OAI
/-! # Resolving every old item of the actual terminal turn chart -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM Calendar
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {h W k attempts edges w R : ℕ} (S : PurchaseSampler)

def loadMeta (base : ℕ) (order : Fin R≃Edges S h (2^W) k) (attempts edges : ℕ) (m : Memory w) :=
  let N := Fintype.card (Old h W k edges)
  fillSegment base (7*N) (fun a=>let q:=a-base
    if hi:q/N<7 then if hr:q%N<N then (metadataTable S order attempts edges ⟨q/N,hi⟩ ⟨q%N,hr⟩:Word w) else 0 else 0) m

theorem metadata_read (base : ℕ) (order : Fin R≃Edges S h (2^W) k) (attempts edges : ℕ) (m : Memory w)
    (r : Fin (Fintype.card (Old h W k edges))) (field : Fin 7) (room : Fintype.card (Old h W k edges)≤2^w) :
    («meta» base (Fintype.card (Old h W k edges)) field).eval (loadMeta S base order attempts edges m) (r.val:Word w)=
      ((metadataTable S order attempts edges field r):Word w) := by
  let N := Fintype.card (Old h W k edges)
  apply RoleROM.read _ .row _ r room rfl
  intro i
  have positive : 0<N := Nat.zero_lt_of_lt i.isLt
  have bound:=Nat.mul_le_mul_right N field.isLt
  rw [Nat.succ_mul] at bound
  have hit : base≤base+field.val*N+i.val ∧ base+field.val*N+i.val<base+7*N := by have:=i.isLt;omega
  have div : (field.val*N+i.val)/N=field.val := by rw [Nat.add_comm,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt i.isLt,Nat.zero_add]
  have rem : (field.val*N+i.val)%N=i.val := Nat.mul_add_mod_of_lt i.isLt
  have offset : base+field.val*N+i.val-base=field.val*N+i.val := by omega
  dsimp only [N] at hit offset div rem
  simp only [loadMeta,fillSegment,ite_eq_left hit,offset,div,rem,dite_eq_left field.isLt,dite_eq_left i.isLt]

theorem normalized_site (L : Chart) (raw : Bool→Socket) (p : Bool→Public S h W k attempts)
    (m : Memory w) (r : Word w) (seen : ∀b,Resolved S L (raw b) m r (p b))
    (room : siteLast h (2^W) k+1≤2^w) (side : Bool) :
    let b := if name (site S (p false))<name (site S (p true)) then side else !side
    Resolved S L (normalized L raw side) m r (p b) := by
  have lt : ((socketSite L (raw false)).eval m r<(socketSite L (raw true)).eval m r) ↔
      name (site S (p false))<name (site S (p true)) := by
    rw [(seen false).1,(seen true).1,Fin.lt_def,Fin.val_cast_of_lt ((name (site S (p false))).isLt.trans_le room),
      Fin.val_cast_of_lt ((name (site S (p true))).isLt.trans_le room)]
    rfl
  have operands (f : Socket→Expr) (agree : ∀x y op,f (zipSocket op x y)=op (f x) (f y)) :
      (f (normalized L raw side)).eval m r=(f (raw (if name (site S (p false))<name (site S (p true)) then side else !side))).eval m r := by
    by_cases order:name (site S (p false))<name (site S (p true)) <;> cases side <;>
      simp [normalized,agree,sortedRead,Expr.eval,Comparison.test,lt,order]
  let dest:=raw (if name (site S (p false))<name (site S (p true)) then side else !side)
  have key:=operands Socket.ordinal (fun _ _ _=>rfl)
  have tag:=operands Socket.positive (fun _ _ _=>rfl)
  have g:=operands Socket.group (fun _ _ _=>rfl)
  have s:=operands Socket.slot (fun _ _ _=>rfl)
  let b:=if name (site S (p false))<name (site S (p true)) then side else !side
  have pos : (socketSite L (normalized L raw side)).eval m r=(socketSite L (raw b)).eval m r := by
    simp only [b,socketSite,choose,SiteROM.siteExpr,RoleROM.expr,Expr.eval,key,tag,g,s]
    by_cases cmp : name (site S (p false))<name (site S (p true)) <;> simp only [cmp,ite_true,ite_false]
  have numeral : (socketCode L (normalized L raw side)).eval m r=(socketCode L (raw b)).eval m r := by
    simp only [b,socketCode,choose,RoleROM.positiveKey,RoleROM.expr,Expr.eval,key,tag,g,s]
    by_cases cmp : name (site S (p false))<name (site S (p true)) <;> simp only [cmp,ite_true,ite_false]
  exact ⟨pos.trans (seen b).1,numeral.trans (seen b).2⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
