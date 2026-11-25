import OAI.Hierarchy.DescentCalibratedPhysicalStartup
import OAI.Hierarchy.DescentNamedInitialCircuit
import OAI.Hierarchy.DescentNamedWideOriginalInvoice
import OAI.Hierarchy.DescentNamedShellAddress
import OAI.Hierarchy.DescentWideInitialDimensions

namespace OAI
/-! # Initial physical host costs on the same cofinal input and compiler width -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentPackedEpochShelves DescentPackedProfileInstall DescentSeedRoot DescentWideSeedFlags
open DescentExterior DescentTerminalEpochDecoder CorrectionFrame Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing Filter
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B ratio : ℕ)
local notation "a" => localSocketRate G t g
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "k_" J:arg => groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "S_" J:arg x:arg => stageNumbers G t J f g reset (ShellSource.sites x) (tail τ J)

/-- The full startup charge for every original input admitted at one height. -/
def OriginalInitialPriceAt (h : ℕ) : Prop :=
  ∀ x : ShellSource F h,2^h ≤ x.sites →
      let J:=Nat.log 2 h/(2*B)
      let S:=S_ J x
      let k:=k_ J
      let j:=headChunk G S
      let rest:=headRest G S k (tail τ J)
      let q:=2^j*(G.b^(t*J)*G.b)
      let W:=NativeBranch.binLimit (k:=k) S
      let piece:=h/(16*(q*W))
      let p:=W*piece
      let s:=S.firstWidth G.b p
      let w:=ratio*h
      let E:=Fintype.card (Port x.ports x.X.width)
      ∀ (cut n H C K codes extraRate : ℕ) (cfg : DescentTerminalCompiledPrefix.Shape)
        (ordinary : OrdinaryRates G S k cut)
        (resetRate : ResetRates G S k (atRound t) n H C f g cut (tail τ J))
        (branch : G.b ≤ 2^S.capGain) (pos : 0 < p)
        (shrink : reentryRate H C*(1-(2-G.rate)/4)^t ≤ 1/2) (fit : s<2^w),
      let ch:=normalizedPackedChart x.X G S ordinary resetRate branch pos x.opened shrink w fit
      letI : Fintype ch.Pin := ch.finite
      let R:=S.copies
      let ext:=Port ((R*s)*x.ports) (copiesWidth (R*s) x.X.width)
      let all:=DescentTerminalFullPins.Candidate (ch.Pin⊕Hidden E j rest s) K W q piece cfg.terminal.plane.rawRows
      let net:=wideChoiceCircuit (K:=K) (W:=W) (q:=q) (piece:=piece) x.X G S ordinary resetRate branch pos
        x.opened shrink w fit (j:=j) (rest:=rest) cfg
      let gr:=grain (h/2) G.C
      let lo:=selectorBase x.X R s h ch.layout.length
      let front:=end_ (lo+extent gr ch.layout) G.C gr+17*DescentExteriorShelf.span j rest s E
      let extra:=DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.terminal.plane.publicRows
      let fund:=(R*s)*(x.sites+2^J*E)
      extra*w*2^J ≤ extraRate*fund →
      (4*(net.cells+net.internal)+Fintype.card all+Fintype.card ext+(front+extra)*(h+1))*2^J ≤
        (5+extraRate+(1135*(ratio+1)+extraRate))*fund

/-- The threshold is fixed before the original graph, its support cardinality,
the chosen histories and the sixteen purchased appendix banks. -/
theorem original_initial_price_at (large : 20 ≤ B) (reserve : 2*a ≤ τ)
    (advert : 2*(a+(τ+κ+4))+Nat.clog 2 G.b*(t+1) ≤ B)
    (tailFit : 0+0+3+(a+5) ≤ τ)
    (widthFit : 2*((2+hostRate t reset*(t+1)+((t+1)*(hostRate t reset+capRate G t g+1)+11)+
      (0+1)+1)+5+a) ≤ B) (bus : 2 ≤ ratio) :
    ∀ᶠ h : ℕ in atTop,OriginalInitialPriceAt G t f g reset τ B ratio h :=by
  filter_upwards [calibrated_physical_initial_bill G t f g reset τ B ratio large reserve advert tailFit widthFit bus]
    with h paid
  intro x lower J S k j rest q W piece p s w E cut n H C K codes extraRate cfg ordinary resetRate branch pos shrink fit
    ch R ext all net gr lo front extra fund appendix
  let _ : Fintype ch.Pin := ch.finite
  obtain ⟨dates,seats⟩:=issued_wide_shape x.X G S ordinary resetRate branch pos x.opened shrink w fit
  exact paid x.sites lower x.X x.opened ch.Pin ch.layout ch.seed dates seats
    (packedChart_card x.X G S ordinary resetRate branch pos x.opened shrink w fit)
    K codes cfg.terminal.plane.rawRows cfg.terminal.plane.publicRows extraRate appendix

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
