import OAI.Hierarchy.DescentWidePhysicalInitialBill
import OAI.Hierarchy.DescentWideInitialDimensions

namespace OAI
/-! # Cofinal startup cost of the original marked circuit, its selector tape and its external ports -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentSeedRoot DescentTerminalEpochChart
open DescentPackedEpochShelves DescentPackedProfileInstall DescentWideSeedFlags DescentTerminalEpochDecoder
open DescentExterior CorrectionFrame Catalyst Filter
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B ratio : ℕ)
local notation "a" => localSocketRate G t g
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "k_" J:arg => groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)

theorem calibrated_physical_initial_bill (large : 20 ≤ B) (reserve : 2*a ≤ τ)
    (advert : 2*(a+(τ+κ+4))+Nat.clog 2 G.b*(t+1) ≤ B)
    (tailFit : 0+0+3+(a+5) ≤ τ)
    (widthFit : 2*((2+hostRate t reset*(t+1)+((t+1)*(hostRate t reset+capRate G t g+1)+11)+
      (0+1)+1)+5+a) ≤ B) (bus : 2 ≤ ratio) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M,2^h ≤ M →
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=k_ J
      let j:=headChunk G S
      let rest:=headRest G S k (tail τ J)
      let q:=2^j*(G.b^(t*J)*G.b)
      let W:=NativeBranch.binLimit (k:=k) S
      let piece:=h/(16*(q*W))
      let s:=S.firstWidth G.b (W*piece)
      let w:=ratio*h
      ∀ {cp nP : ℕ} (X : Approximation F cp nP),10*(X.size+1) ≤ M →
      ∀ (A : Type) [Fintype A] (ss : List (Source A)) (seed : Select X S.copies s → A),
      ss.length ≤ S.length → seatBill ss ≤ S.length*S.batch →
      Fintype.card A ≤ 80*S.copies*(X.size+1)*(s.log2+1)+(S.length*S.batch)*DescentTerminalEpochBits.width G.C →
      ∀ K codes rows pub extraRate,
      let E:=Fintype.card (Port nP X.width)
      let R:=S.copies
      let All:=DescentTerminalFullPins.Candidate (A⊕Hidden E j rest s) K W q piece rows
      let net:=DescentTerminalSeedChip.circuit X (fun i : Select X R s => (Sum.inl (Sum.inl (Sum.inl (seed i))) : All))
      let ext:=Port ((R*s)*nP) (copiesWidth (R*s) X.width)
      let gr:=grain (h/2) G.C
      let front:=end_ (selectorBase X R s h ss.length+extent gr ss) G.C gr+17*DescentExteriorShelf.span j rest s E
      let extra:=DescentTerminalPublicIdentity.total K W q piece codes rows pub
      let fund:=(R*s)*(M+2^J*E)
      extra*w*2^J ≤ extraRate*fund →
      (4*(net.cells+net.internal)+Fintype.card All+Fintype.card ext+(front+extra)*(h+1))*2^J ≤
        (5+extraRate+(1135*(ratio+1)+extraRate))*fund := by
  filter_upwards [original_initial_dimensions G t f g reset τ B ratio large reserve advert tailFit widthFit bus]
    with h measured
  intro J M lower S k j rest q W piece s w cp nP X room A _ ss seed dates seats pins K codes rows pub extraRate
    E R All net ext gr front extra fund appendix
  obtain ⟨host,floor,first,Rpos,seedWidth,profile,port,support,copies,bulk,time,mode,wide,paid⟩:=measured M lower
  have sites : S.initialSites=M := rfl
  dsimp only [net,ext,All,front,extra,fund,gr,E,R]
  simpa only [Nat.one_mul,Nat.mul_one,sites] using
    (physical_initial_bill X S s h G.C w ss seed (j:=j) (rest:=rest) (K:=K)
      (W:=W) (q:=q) (piece:=piece) (codes:=codes) (rows:=rows) (pub:=pub)
      (ratio+1) (2^J) B 1 h 1 extraRate room dates seats pins host (by omega) rfl floor first Rpos
      seedWidth profile port (Nat.mul_le_mul_right h (Nat.le_succ ratio)) support copies bulk time mode
      (by simpa only [Nat.one_mul] using wide) paid appendix)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
