import OAI.Hierarchy.TaggedWireCursorTerm
import OAI.Hierarchy.TaggedWireRouting

namespace OAI
/-! # One native routing on all tags from their actual original calendar traces -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical BigOperators

variable {F : Type*} {X : Type} [Field F] {h d k w R M den : ℕ}
    (slots : Event→Slot X) (es : List Event) (state : Equiv.Perm (Tagged.Row h)→X)

/-- Only the reachable native replacement identities and their observed
terminal inventory enter. The full tagged routing and selector encoder are derived. -/
structure CalendarTerms (F : Type*) [Field F] (h d k w R M den : ℕ) (slots : Event→Slot X)
    (es : List Event) (state : Equiv.Perm (Tagged.Row h)→X) where
  width : ∀p {tail x},WireTelescope.CalendarTape.Prefix slots es (state p) tail x→Widths (siteLast h d k+1)
  head : ∀p,exposedWidth p d k w R=width p WireTelescope.CalendarTape.Prefix.start
  operator : ∀p {e tail x}(t:WireTelescope.CalendarTape.Prefix slots es (state p) (e::tail) x)(c:(slots e).choice x),
    SiteMatrix (State (width p t)) (State (width p (WireTelescope.CalendarTape.Prefix.advance t c))) F
  step : ∀p {e tail x}(t:WireTelescope.CalendarTape.Prefix slots es (state p) (e::tail) x) v,(raw F (width p t)).coeff v=
    ∑c,SiteMatrix.act (operator p t c) (raw F (width p (WireTelescope.CalendarTape.Prefix.advance t c))).coeff v
  reported : ∀p (j : Path slots es (state p)),Report p d k w R M den (width p (WireTelescope.CalendarTape.Prefix.finish WireTelescope.CalendarTape.Prefix.start j))

namespace CalendarTerms
variable {slots es state} (Z : CalendarTerms F h d k w R M den slots es state)

theorem port_compat : (boardLayout h d k w R).port ∘ routingPort=exposedSite h d k w R :=
  outer_routing (siteNumber h d k) (reserveColumn h d k R)

private def renameOuter {s : ℕ} {I B : Type} [Fintype I] [Fintype B]
    {f : (I→Bool)→F} {u v : I→Fin s} {width : B→Widths s} (same : u=v)
    (family : Expansion ((CorrectionProducts.raw f).group v) B width) :
    Expansion ((CorrectionProducts.raw f).group u) B width := same.symm ▸ family

private theorem renameOuter_eval {s : ℕ} {I B : Type} [Fintype I] [Fintype B]
    {f : (I→Bool)→F} {u v : I→Fin s} {width : B→Widths s} (same : u=v)
    (family : Expansion ((CorrectionProducts.raw f).group v) B width) (j : B) (x : I→Bool) :
    onPins (renameOuter same family) j x=onPins family j x := by
  subst v
  rfl

def realFamily (p : Equiv.Perm (Tagged.Row h)) :
    Expansion ((CorrectionProducts.raw (routingMatch (F:=F) p)).group ((boardLayout h d k w R).port ∘ routingPort))
      (Path slots es (state p)) (fun j=>installedWidths (Z.reported p j).geometry.links.ends (Z.reported p j).geometry.links.bits) :=
  renameOuter port_compat (actualFamily p (Z.width p) (Z.operator p) (Z.step p) (Z.head p) (Z.reported p))

/-- Every tag shares the public board, reserve width and exact binary tape
length. Only its original baseline, signed terms and observed edge records vary. -/
def nativeRouting (Shared : Type) [Fintype Shared] : Tagged.NativeRouting F k h w M :=
  WireTelescope.native (D:=boardLayout h d k w R) (hist:=fun p=>Path slots es (state p)) Shared (fun p=>encode slots es (state p))
    (fun p j=>(Z.reported p j).geometry.links) Z.realFamily

theorem encoding_iff (Shared : Type) [Fintype Shared] (p : Equiv.Perm (Tagged.Row h)) (raw : Bits (bits slots es)) :
    (∃!i:Fin ((Z.nativeRouting Shared).count p),(Z.nativeRouting Shared).encoding p i=raw) ↔
      ∃!j:Path slots es (state p),encode slots es (state p) j=raw := by
  let E:=Fintype.equivFin (Path slots es (state p))
  constructor
  · rintro ⟨i,hi,_⟩
    refine ⟨E.symm i,hi,fun j hj=>(encode slots es (state p)).injective (hj.trans hi.symm)⟩
  · rintro ⟨j,hj,_⟩
    have same : (Z.nativeRouting Shared).encoding p (E j)=encode slots es (state p) j :=
      congrArg (encode slots es (state p)) (E.symm_apply_apply j)
    exact ⟨E j,same.trans hj,fun i hi=>((Z.nativeRouting Shared).encoding p).injective (hi.trans (same.trans hj).symm)⟩

theorem retained_links (Shared : Type) [Fintype Shared] (p : Equiv.Perm (Tagged.Row h)) (i : Fin ((Z.nativeRouting Shared).count p)) :
    (Z.nativeRouting Shared).links ⟨p,i⟩=(Z.reported p ((Fintype.equivFin (Path slots es (state p))).symm i)).geometry.links := rfl

/-- The scalar of each routed summand is evaluated by its authentic terminal
report and the signed prefix matrices at every earlier physical party. -/
theorem route_pins (Shared : Type) [Fintype Shared] (p : Equiv.Perm (Tagged.Row h)) (i : Fin ((Z.nativeRouting Shared).count p))
    (x : OpenPins h w (fun _ : Fin k=>Fintype.card (Columns h d)*R)→Bool) :
    (Z.nativeRouting Shared).route ⟨p,i⟩ x=
      onPins (actualFamily p (Z.width p) (Z.operator p) (Z.step p) (Z.head p) (Z.reported p))
        ((Fintype.equivFin (Path slots es (state p))).symm i) (x ∘ routingPort) :=
  renameOuter_eval port_compat _ _ _

end CalendarTerms
end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm

end
end OAI
