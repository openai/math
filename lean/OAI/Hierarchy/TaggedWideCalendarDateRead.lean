import OAI.Hierarchy.TaggedWideCalendarPassiveRead
import OAI.Hierarchy.TaggedWideCalendarGatherRead

namespace OAI
/-! # Dated matrix coefficients on the actual native branch selector -/

noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 500000
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU SiteScatter
open scoped Classical BigOperators
private def rowBlock {K n : ℕ} (U : Fin n → Widths K) (base : Widths K) (s : Fin K)
    (z : State (base+∑i,U i) s) (i : Fin n) : State (U i) s :=
  blockPortState U s (splitPortState base (∑j,U j) s z).2 i

private abbrev siteWidth {K : ℕ} (s : Fin K) (g : Widths K) (p : (portGraph K).Port s) : ℕ := g p.val.1

private abbrev combined {K n : ℕ} (g : Fin n → Widths K) : Widths K := ∑i,g i

private abbrev pinsValue {Ex Sel D : Type} (G : Gate) (out : Memory G.W)
    (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool) : SitePins Ex Sel D G → Bool :=
  Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

private abbrev fieldAt {T deg W : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (out : Memory W) (f : SiteControls.Field deg) : ℕ := (out (controlAddress P work j s f)).val

/-- The original paid ballot selects the party, while every unaffected bit is checked
against its predecessor in the authentic comparison page. -/
theorem datedProgram_value {F Ex Sel D A : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width n formats digits C : ℕ} (P : Dated T) (work : ℕ)
    (j : Fin T) (s : Fin P.sites) (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val)
    (inside : ∀f : SiteControls.Field deg,controlAddress P work j s f<G.u)
    {J : Fin n→Type} [∀i,Fintype (J i)] (demand : Fin n→Widths P.sites)
    (installed : ∀i,J i→Widths P.sites) (M : ∀i c,SiteMatrix (State (demand i)) (State (installed i c)) F)
    (rest : Widths P.sites) (c : ∀i,J i)
    (x : State (rest+combined demand) s) (y : State (rest+combined (fun i=>installed i (c i))) s)
    (l : PassiveWindow.Parts ((portGraph P.sites).Port s) (Fin deg) width
      (fun p => siteWidth s rest p + siteWidth s (combined demand) p))
    (r : PassiveWindow.Parts ((portGraph P.sites).Port s) (Fin deg) width
      (fun p => siteWidth s rest p + siteWidth s (combined (fun i=>installed i (c i))) p))
    (words : Bool→Fin deg→Fin width→SitePins Ex Sel D G⊕Bool) (fit : formats+1≤2^digits)
    (ballotRoom : ballotAddress P work j s 0<G.u) (small : digits≤G.W+1)
    (packet : Fin formats→BitNetwork F (Fintype.card (SitePins Ex Sel D G)))
    (place : A↪Fin P.sites) (ballot : A→Fin n) (kind : A→Fin formats)
    (word : A→Fin C→Word G.W) (header : Fin C) (selector : ∀t,(word t header).val=(kind t).val+1)
    (published : out (ballotAddress P work j s 0)=table place word s header)
    (source : ∀i p,l.owner i=some p→∀u:Fin (l.width i),
      Sum.elim (pinsValue G out ext sel data) id (words false i (u.castLE (l.within i))) =
        (x p).val.testBit (l.base i+u.val))
    (target : ∀i p,r.owner i=some p→∀u:Fin (r.width i),
      Sum.elim (pinsValue G out ext sel data) id (words true i (u.castLE (r.within i))) =
        (y p).val.testBit (r.base i+u.val))
    (lengthRead : ∀i q,fieldAt P work j s out (.inr ((i,q),0))=(PassiveWindow.header width (l.view (siteWidth s (combined demand)) i)
        (r.view (siteWidth s (combined (fun a=>installed a (c a)))) q)
        (PassiveWindow.linked (siteWidth s rest) (siteWidth s (combined demand))
          (siteWidth s (combined (fun a=>installed a (c a)))) l r i q)).val)
    (startRead : ∀i q (side : Bool),fieldAt P work j s out (.inr ((i,q),if side then 2 else 1))=
      (PassiveWindow.heads width (l.view (siteWidth s (combined demand)) i)
        (r.view (siteWidth s (combined (fun a=>installed a (c a)))) q) side).val)
    (signed : ∀t,place t=s →
      TypedWiring.value (P:=SitePins Ex Sel D G) (packet (kind t)) (pinsValue G out ext sel data) =
      M (ballot t) (c (ballot t)) s (rowBlock demand rest s x (ballot t))
        (rowBlock (fun i=>installed i (c i)) rest s y (ballot t)))
    (apart : ∀i,(∀t,place t=s→ballot t≠i)→M i (c i) s (rowBlock demand rest s x i)
      (rowBlock (fun a=>installed a (c a)) rest s y i)=1) :
    TypedWiring.value (P:=SitePins Ex Sel D G)
        (datedProgram (Ex:=Ex) (Sel:=Sel) (D:=D) (F:=F) G P work j s fit words ballotRoom small packet)
        (pinsValue G out ext sel data) = matrix M rest c s x y := by
  apply dated_eval M _ packet _ fit place ballot kind word header selector
    (pinsValue G out ext sel data) rest c s x y
  · intro b
    exact (dateMode_read G P work j s ballotRoom small out ext sel data b dense).trans
      (congrArg (fun w : Word G.W=>w.val.testBit b.val) published)
  · exact passiveNet_value G P work j s out ext sel data dense inside rest
      (combined demand) (combined (fun i=>installed i (c i))) x y l r words source target lengthRead startRead
  · exact signed
  · exact apart


end Hierarchy.WireTelescope.PassMatrix

end
end OAI
