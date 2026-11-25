import OAI.Hierarchy.ProtocolRAMBankAgreement
import OAI.Hierarchy.ProtocolRAMColumnReaderBounds
import OAI.Hierarchy.ProtocolRAMCatalogueMount

namespace OAI
/-! # The acquired endpoints read only the public directory and the DFS tile banks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CatalogueRows
open scoped Classical Fin.CommRing
variable {w attempts : ℕ}

private theorem select_banks {ok : Bank→Prop} (limit : ℕ)
    (pub : ∀ b : Bank, b.base+b.size≤limit → ok b)
    (head : StockCommit.PortHeader) (ends : head.stop≤limit)
    {n : ℕ} (xs : Fin n→Expr) (terms : ∀i,(xs i).UsesBanks ok) :
    (select head xs).UsesBanks ok := by
  have stop : head.start+2*head.small+2*head.large≤limit := by
    simp only [StockCommit.PortHeader.stop,StockCommit.PortHeader.parity,StockCommit.PortHeader.owner] at ends
    omega
  have field : head.fieldTerm.UsesBanks ok :=
    ⟨pub _ (by change head.start+head.small+head.small≤limit;omega),trivial⟩
  have ball : head.ballTerm.UsesBanks ok :=
    ⟨pub _ (by change head.start+head.small≤limit;omega),trivial⟩
  exact Expr.UsesBanks.choose n 0 _ _ (fun i=>Expr.UsesBanks.at_row _ _ (terms i) field) ball

/-- Both endpoints are read on every padded candidate, even with a zero or
malformed candidate key. Neither historical ballots nor archive flags are operands. -/
theorem Directory.endpoint_words (v : Directory attempts) (S : PurchaseSampler) (h W k depth K G H limit : ℕ)
    (m m' : Memory w)
    (outer : (v.header h (2^W) k S.degree depth).stop≤limit)
    (keys : (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase).stop≤limit)
    (C : ColumnROM.Cover h W v.remapBase v.sitesBase v.superBase K G H limit)
    (low : ∀x, x<limit → m x=m' x)
    (tiles : ∀a (i : Key h (2^W) k) x, let b:=((v.shelf a).L S depth i).source
      b.base≤x → x<b.base+b.size → m x=m' x) (r : Word w) :
    let src:=v.source S h W k depth K G H
    src.left.eval m r=src.left.eval m' r ∧ src.right.eval m r=src.right.eval m' r := by
  let ok := fun b : Bank => ∀ j : Word w, b.read m j=b.read m' j
  have pub (b : Bank) (e : b.base+b.size≤limit) : ok b :=
    b.read_eq_on m m' (fun x _ below=>low x (below.trans_le e))
  have paths (a : Fin attempts) (i : Key h (2^W) k) (j : Fin (depth+1)) :
      (readTile (v.shelf a) S depth i j).UsesBanks ok :=
    ⟨Bank.read_eq_on _ m m' (tiles a i),trivial,trivial⟩
  have ct (i : Key h (2^W) k) (j : Fin 3) :
      ok (Native.stageBank h (2^W) (stageNumber (stage i)) j) :=
    pub _ ((Native.stageBank_end h (2^W) (stageNumber (stage i)) j).trans C.ct)
  have leaf (a : Fin attempts) (i : Key h (2^W) k) (side : Bool) :
      let f:=keyFields v.remapBase (v.shelf a) S depth i a side
      f.group.UsesBanks ok ∧ f.port.UsesBanks ok := by
    refine ⟨⟨pub _ ((remap_end v.remapBase (stage i)).trans C.names),ct i 0,paths a i 0⟩,?_⟩
    cases side
    · exact ⟨ct i 1,paths a i _⟩
    · exact ⟨ct i 2,paths a i _⟩
  have localWord (a : Fin attempts) (side : Bool) :
      let f:=event v.remapBase v.keysBase (v.shelf a) S h (2^W) k depth a side
      f.group.UsesBanks ok ∧ f.port.UsesBanks ok ∧ f.tag.UsesBanks ok :=
    ⟨select_banks limit pub _ keys _ (fun i=>(leaf a i side).1),
     select_banks limit pub _ keys _ (fun i=>(leaf a i side).2),trivial⟩
  have words (side : Bool) :
      let f:=v.fields S h W k depth side
      f.group.UsesBanks ok ∧ f.port.UsesBanks ok ∧ f.tag.UsesBanks ok :=
    ⟨select_banks limit pub _ outer _ (fun a=>(localWord a side).1),
     select_banks limit pub _ outer _ (fun a=>(localWord a side).2.1),
     select_banks limit pub _ outer _ (fun a=>(localWord a side).2.2)⟩
  have endSuper:=C.super
  have groups : ok (ProtocolRAMSupergroupDirectory.groupBank v.superBase K) :=
    pub _ (by change v.superBase+ProtocolRAMSupergroupDirectory.span K≤limit;omega)
  have offsets : ok (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K) :=
    pub _ (by change v.superBase+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤limit;omega)
  have endAt (side : Bool) :
      let f:=v.fields S h W k depth side
      (SiteROM.atPort v.sitesBase G H v.superBase K (ReportSockets.copies k attempts) f.group f.port f.tag).UsesBanks ok := by
    obtain ⟨g,p,t⟩:=words side
    exact ⟨pub _ C.sites,⟨pub _ C.offsets,groups,g⟩,⟨offsets,g⟩,Expr.UsesBanks.scale 1 _
      ⟨t,Expr.UsesBanks.scale _ _ p⟩⟩
  exact ⟨Expr.UsesBanks.read _ (endAt false) (fun _ h=>h) r,
    Expr.UsesBanks.read _ (endAt true) (fun _ h=>h) r⟩

end Hierarchy.ProtocolRAM.BoughtSockets

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard LinearAlgebra.SpectralBooks
open scoped Fin.CommRing

theorem Board.coreMount_agree {h W w k K : ℕ} {S : PurchaseSampler} (b : Board) (π : Equiv.Perm (Fin (2^h)))
    (place : Site h (2^W) k→Fin K) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (m m' : Memory w) (ends : ∀ r : Word w, b.bought.left.eval m r=b.bought.left.eval m' r ∧
      b.bought.right.eval m r=b.bought.right.eval m' r) :
    (b.coreMount π place order m).actual=(b.coreMount π place order m').actual := by
  apply congrArg₂ PortGraph.mk
  · apply congrArg (b.byKind _)
    funext j
    simp only [BoughtSource.view,(ends (j.val:Word w)).1,(ends (j.val:Word w)).2]
  · apply congrArg (b.byKind _)
    funext j
    simp only [BoughtSource.view,(ends (j.val:Word w)).1,(ends (j.val:Word w)).2]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
