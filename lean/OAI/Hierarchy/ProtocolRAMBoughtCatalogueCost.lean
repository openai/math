import OAI.Hierarchy.ProtocolRAMRowChoiceWork
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Input-size independent cost of the acquired endpoint expressions -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open ProbeStage PurchaseFrozen ReportSockets Calendar CatalogueRows
noncomputable section

private theorem substitute (x j : Expr) : (x.atRow j).work≤x.work*(j.work+1) := by
  induction x <;> simp only [Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega

def selectWork (n u : ℕ) := 1+n*(9+8*u)

theorem select_work (h : StockCommit.PortHeader) {n u : ℕ} (xs : Fin n→Expr)
    (small : ∀i,(xs i).work≤u) : (select h xs).work ≤ selectWork n u := by
  have fit i : ((xs i).atRow h.fieldTerm).work≤8*u := by
    have a := substitute (xs i) h.fieldTerm
    change _≤(xs i).work*8 at a
    have b:=small i
    omega
  apply (choose_work_bound n 0 (8*u) _ h.ballTerm fit).trans_eq
  simp [selectWork,StockCommit.PortHeader.ballTerm,Expr.work,Nat.add_comm]; omega

theorem event_work {z d k attempts : ℕ} (groupBase keyBase depth : ℕ) (sh : Shelf) (S : PurchaseSampler)
    (a : Fin attempts) (s : Bool) : let x:=event groupBase keyBase sh S z d k depth a s
    let U:=selectWork (count z d k) 19
    x.group.work≤U ∧ x.port.work≤U ∧ x.tag.work≤U := by
  intro x U
  refine ⟨select_work _ _ (fun _=>by change 19≤19;decide),select_work _ _ (fun _=>by change 14≤19;decide),?_⟩
  change 1≤1+_
  omega

private theorem scale_work (n : ℕ) (x : Expr) : (ProtocolRAM.scale n x).work=1+n*(x.work+1) := by
  induction n with
  | zero => simp [ProtocolRAM.scale,Expr.work]
  | succ n ih => simp only [ProtocolRAM.scale,Expr.work,ih,Nat.succ_mul];omega

def wordWork (d k attempts : ℕ) :=
  let U:=selectWork attempts (7+selectWork ((2*rounds d+1)*(2*k)) 19)
  50+(4+ReportSockets.copies k attempts)*(U+1)

theorem Directory.source_work {attempts : ℕ} (v : Directory attempts) (S : PurchaseSampler)
    (z W k depth K G H : ℕ) : (v.source S z W k depth K G H).All (fun e=>e.work≤wordWork (2^W) k attempts) := by
  let perKey:=7+selectWork (count z (2^W) k) 19
  let U:=selectWork attempts perKey
  let c:=ReportSockets.copies k attempts
  let f:=v.fields S z W k depth
  have field (s : Bool) : (f s).group.work≤U ∧ (f s).port.work≤U ∧ (f s).tag.work≤U := by
    refine ⟨select_work _ _ (fun a=>((event_work v.remapBase v.keysBase depth (v.shelf a) S a s).1).trans (Nat.le_add_left ..)),
      select_work _ _ (fun a=>((event_work v.remapBase v.keysBase depth (v.shelf a) S a s).2.1).trans (Nat.le_add_left ..)),
      select_work _ _ (fun a=>((event_work v.remapBase v.keysBase depth (v.shelf a) S a s).2.2).trans (Nat.le_add_left ..))⟩
  have atPort (s : Bool) : (SiteROM.atPort v.sitesBase G H v.superBase K c (f s).group (f s).port (f s).tag).work≤50+(4+c)*(U+1) := by
    obtain ⟨hg,hp,ht⟩ := field s
    have scaled := Nat.mul_le_mul_left c (Nat.add_le_add_right hp 1)
    simp only [SiteROM.atPort,SiteROM.siteExpr,addressExpr,Expr.work,scale_work,Nat.one_mul]
    rw [Nat.add_mul]
    omega
  have rew : wordWork (2^W) k attempts=50+(4+c)*(U+1) := by
    simp only [wordWork,U,perKey,c,count_eq]
  have big : U+5≤50+(4+c)*(U+1) := by rw [Nat.add_mul];omega
  have archive (base : Fin attempts→ℕ) : (v.archived z (2^W) k S.degree depth base).work≤U := by
    apply select_work
    intro a
    change 7≤7+_
    omega
  rw [rew]
  exact ⟨(Nat.add_le_add_right (field false).1 5).trans big,atPort false,atPort true,
    (archive (v.flagBase)).trans (by omega),(archive (v.menuBase)).trans (by omega)⟩

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
