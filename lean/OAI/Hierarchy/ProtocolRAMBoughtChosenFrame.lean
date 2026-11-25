import OAI.Hierarchy.ProtocolRAMColumnReaderBounds
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Temporal frame for the selected original birth shelf -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CatalogueRows
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

variable {w z W k n : ℕ} (v : Directory n) (S : PurchaseSampler) (depth K G H : ℕ)

private def onlyShelf (a : Fin n) : Directory n :=
  {v with shelf:=fun _=>v.shelf a,flagBase:=fun _=>0,menuBase:=fun _=>0}

private def siteTerm (side : Bool) : Expr :=
  let x:=v.fields S z W k depth side
  SiteROM.atPort v.sitesBase G H v.superBase K (copies k n) x.group x.port x.tag

private theorem siteTerm_congr (m : Memory w) (r : Word w) (base super K G H copies : ℕ) (x y : Inputs)
    (g : x.group.eval m r=y.group.eval m r) (p : x.port.eval m r=y.port.eval m r)
    (t : x.tag.eval m r=y.tag.eval m r) :
    (SiteROM.atPort base G H super K copies x.group x.port x.tag).eval m r=
      (SiteROM.atPort base G H super K copies y.group y.port y.tag).eval m r := by
  simp only [SiteROM.atPort,SiteROM.siteExpr,addressExpr,Expr.eval,eval_scale,g,p,t]

private theorem siteTerm_selected (m : Memory w) (a : Fin n)
    (r : Fin (v.header z (2^W) k S.degree depth).ports)
    (load : (v.header z (2^W) k S.degree depth).Loaded m) (fit : n≤2^w) (side : Bool) :
    let h:=v.header z (2^W) k S.degree depth
    (siteTerm (z:=z) (W:=W) (k:=k) v S depth K G H side).eval m ((h.enum ⟨a,r⟩).val:Word w)=
      (siteTerm (z:=z) (W:=W) (k:=k) (onlyShelf v a) S depth K G H side).eval m ((h.enum ⟨a,r⟩).val:Word w) := by
  intro h
  let term:=fun (b : Fin n) (i : Fin n)=>event v.remapBase v.keysBase (v.shelf b) S z (2^W) k depth i side
  have same (get : Inputs→Expr) :
      (select h (fun i=>get (term i i))).eval m ((h.enum ⟨a,r⟩).val:Word w)=
      (select h (fun i=>get (term a i))).eval m ((h.enum ⟨a,r⟩).val:Word w) :=
    (v.dispatch z (2^W) k S.degree depth m load fit a r (fun i=>get (term i i))).trans
      (v.dispatch z (2^W) k S.degree depth m load fit a r (fun i=>get (term a i))).symm
  exact siteTerm_congr m _ _ _ _ _ _ _ _ _ (same Inputs.group) (same Inputs.port) (same Inputs.tag)

/-- A relative row in any completed birth has the same two physical endpoint
fields at both snapshots. The ordinal may be an inactive candidate. -/
theorem Directory.chosen_view_frame {cut : ℕ} (a : Fin n)
    (r : Fin (v.header z (2^W) k S.degree depth).ports)
    (left right : Memory w) (same : PrefixAgreement.Low cut left right) (word : cut<2^w)
    (rooms : ColumnROM.Cover z W v.remapBase v.sitesBase v.superBase K G H cut)
    (headEnd : (v.header z (2^W) k S.degree depth).stop≤cut)
    (keyEnd : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).stop≤cut)
    (source : ∀i : Key z (2^W) k,((v.shelf a).L S depth i).endAddress≤cut)
    (head : (v.header z (2^W) k S.degree depth).Loaded right) (dates : n≤2^w) :
    let src:=v.source S z W k depth K G H
    let row:=((v.header z (2^W) k S.degree depth).enum ⟨a,r⟩).val
    (src.view left (row:Word w)).left=(src.view right (row:Word w)).left ∧
      (src.view left (row:Word w)).right=(src.view right (row:Word w)).right := by
  intro src row
  let h:=v.header z (2^W) k S.degree depth
  have ports : h.ports≤h.count := Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt a.isLt)
  have enough := ports.trans_lt (ProtocolRAMPurchaseSampler.lt_span h.count)
  have pad : ProtocolRAMPurchaseSampler.span h.ports≤cut := by
    have stop : h.start+2*h.small+h.large+h.large≤cut:=headEnd
    have estimate:=ProtocolRAMPurchaseSampler.span_le h.ports
    change h.ports<h.small at enough
    omega
  have zeroEnd : 0+ProtocolRAMPurchaseSampler.span h.ports≤cut := by
    simpa only [Nat.zero_add] using pad
  have cover : (onlyShelf v a).Cover S z W k depth K G H cut :=
    ⟨headEnd,keyEnd,rooms.ct,rooms.names,fun _=>source,rooms.super,rooms.offsets,rooms.sites,
      fun _=>zeroEnd,fun _=>zeroEnd⟩
  have all:=(onlyShelf v a).source_fits S z W k depth K G H cut word cover
  have before:=head.frame (fun x _ hx=>same x (hx.trans_le headEnd))
  have each (side : Bool) :
      (siteTerm (z:=z) (W:=W) (k:=k) v S depth K G H side).eval left (row:Word w)=
      (siteTerm (z:=z) (W:=W) (k:=k) v S depth K G H side).eval right (row:Word w) := by
    rw [siteTerm_selected v S depth K G H left a r before dates side,
      siteTerm_selected v S depth K G H right a r head dates side]
    apply PrefixAgreement.expr _ _ _ cut _ same
    apply PrefixAgreement.inputEnd_of_fits _
    cases side
    · exact all.2.1
    · exact all.2.2.1
  exact ⟨congrArg Fin.val (each false),congrArg Fin.val (each true)⟩

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
