import OAI.Hierarchy.DescentSpectralPurchasedHosts
import OAI.Hierarchy.DescentFixedHostOperator
import OAI.Hierarchy.DescentStageTerminalRoom
import OAI.Hierarchy.DescentStageStartupPrice
import OAI.Hierarchy.DescentFixedHostISARoom

namespace OAI
/-! # The selected circuit at one dyadic height on the fixed rotor -/
namespace Hierarchy.DescentSixParty.EpochRotor
open DescentCompiler DescentCompiler.TerminalScale Catalyst CatalystSubstitution CorrectionBatch CollapseOracle Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} (c : EpochRotor G)

/-- A host with the copies, grain, reference sockets and tariff of this very input circuit. -/
def ReturnedHost (τ β h M cost : ℕ) {cp n : ℕ} (X : Approximation F cp n) : Prop :=
  let J:=Nat.log 2 h/(2*β)
  let S:=stageNumbers G c.rounds J c.f c.g c.reset M (tail τ J)
  let k:=groupBits c.rounds J S.hostGain S.capGain (cutRate c.rounds c.f c.g)
  let s:=S.firstWidth G.b (headGrain G S k h)
  let copies:=S.copies*s
  let Y:=referenceReplacement (F:=F) h cp
  ∃calls : ℕ, ∃H : Host F cp (copies*n) (Sockets (List.replicate calls (tagCall h Y))),
    Agrees (independentCopies copies X) (tableApprox H.width (exactValue _ H)) ∧
      hostSize H*2^J≤cost*copies*(M+2^J*Fintype.card (Port n X.width))

/-- A constructor at one actual circuit can use every purchased word, all three
mounted table bounds, and the geometry of the concrete rotor at that same height. -/
theorem produces_of_stage_returns (drift limit : ℕ)
    (build : ∀head dates billed last : ℕ, ∃lower : ℕ, ∀W≥lower,
      ∃driftR slots τ₀ : ℕ, ∀τ≥τ₀, ∃β₀ : ℕ, ∀β≥β₀, ∃cost : ℕ, ∀ᶠ h : ℕ in atTop,
        SeedNamed.OriginalWord G c.board c.spec c.rounds c.f c.g c.reset (cutRate c.rounds c.f c.g)
          drift limit c.branch head dates billed last W τ β h driftR slots →
        ∀m : ℕ, let M:=(2:ℕ)^m
          2^h≤M → M≤(2^h)^2 → ∀{cp n : ℕ} (X : Approximation F cp n), 10*(X.size+1)≤M →
          c.HostGeometry τ β h M X →
          TerminalRoomAt G c.spec c.rounds c.f c.g c.reset drift W τ β h M →
          SeedNamed.OriginalPurchaseAt G c.spec c.rounds c.f c.g c.reset c.nodesLog c.degree c.multiplicity
            drift limit W τ β h →
          (let J:=Nat.log 2 h/(2*β)
           let S:=stageNumbers G c.rounds J c.f c.g c.reset M (tail τ J)
           let k:=groupBits c.rounds J S.hostGain S.capGain (cutRate c.rounds c.f c.g)
           SeedNamed.HostWordRoom G S k (tail τ J) (headGrain G S k h) (headChunk G S) W h) →
          SeedNamed.StageDateResources G c.spec c.rounds c.f c.g c.reset drift limit c.nodesLog c.degree
            τ β h M (W*h) →
          ISAFromInvoice G c.rounds c.f c.g c.reset τ β W cost h M X →
          c.ReturnedHost τ β h M cost X) :
    c.ProducesHosts drift limit :=by
  intro head dates billed last
  obtain ⟨floor,make⟩:=build head dates billed last
  refine ⟨max floor 9,?_⟩
  intro W enough
  have word : 9≤W := (le_max_right ..).trans enough
  obtain ⟨driftR,slots,first,makeTail⟩:=make W ((le_max_left ..).trans enough)
  obtain ⟨tGeom,geometry⟩:=c.cofinal_host_geometry
  obtain ⟨tStart,startup⟩:=SeedNamed.cofinal_startup_price G c.spec c.rounds c.f c.g c.reset
    c.nodesLog c.degree c.multiplicity drift limit W c.branch word
  refine ⟨driftR,slots,max first (max tGeom tStart),?_⟩
  intro τ bought
  obtain ⟨bMake,makeBus⟩:=makeTail τ ((le_max_left ..).trans bought)
  have together : max tGeom tStart≤τ := (le_max_right ..).trans bought
  obtain ⟨bGeom,geometryBus⟩:=geometry τ ((le_max_left ..).trans together)
  obtain ⟨bStart,startBus⟩:=startup τ ((le_max_right ..).trans together)
  obtain ⟨bRoom,rooms⟩:=cofinal_terminal_room G c.spec c.rounds c.f c.g c.reset drift W τ c.branch (by omega)
  refine ⟨max (max bMake bStart) (max bGeom bRoom),?_⟩
  intro β paid
  have receipts : max bMake bStart≤β := (le_max_left ..).trans paid
  have both : max bGeom bRoom≤β := (le_max_right ..).trans paid
  obtain ⟨cost,emit⟩:=makeBus β ((le_max_left ..).trans receipts)
  have isa:=cofinal_isa_from_invoice G c.rounds c.f c.g c.reset τ β W cost (by omega)
  refine ⟨cost,?_⟩
  filter_upwards [emit, geometryBus β ((le_max_left ..).trans both),
    rooms β ((le_max_right ..).trans both), startBus β ((le_max_right ..).trans receipts),isa] with h compile geometryAt paidAt prices isaAt
  intro original
  dsimp only [DyadicHostAt]
  intro m lo hi cp n X fits
  have ⟨geometryX⟩:=geometryAt (M:=2^m) X fits
  exact compile original m lo hi X fits geometryX (paidAt (2^m)) prices.1
    (prices.2.1 (2^m) last lo hi original.finalFits) (prices.2.2 (2^m) lo hi)
    (isaAt (2^m) hi X fits)

end
end Hierarchy.DescentSixParty.EpochRotor

end OAI
