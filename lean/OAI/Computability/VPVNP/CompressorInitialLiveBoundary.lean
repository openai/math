import OAI.Computability.VPVNP.CompressorInitialPhysicalBoundary
import OAI.Computability.VPVNP.CompressorInitialClocks

/-! # The complete live startup and initial descriptor boundary

Starting with the pair tag prepared by the auxiliary copy, the physical
eleven-word table executes its eight startup calls and four cursor rows
on their actual consecutive memories. The proof uses the same smaller
clock as all selected shrinking and refresh rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ScheduledTrace

universe v

open BurstRAM Compression DescriptorSpace BlockPlanner Schedule CursorBounds CursorNetwork CursorRouting
open LiveProgram LiveProgram.CompressedPair PairSimulation.LocalHistory PairSimulation.TraversalRows PairSimulation.TraversalRoles
open Filter
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
  (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockClock.small sourceCap
  InitialTransferred.bootstrap CursorBounds.virtualBits CursorBounds.initialWidth CursorBounds.initialPositions
  CursorNetwork.cursorState

/-- The pair startup and four cursor visits, with the typed state at the first selected pass. -/
def InitialLive (p q addr n base clk : ℕ) (terminal : PairTable) (pub : Fin 11 → Word (wordBits addr n))
    (incoming : Memory (wordBits addr n)) (hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0)) : Prop :=
  let boot := InitialTransferred.bootstrap B p q
  let A := BlockProgram.script B
  let T := roundedDown p q n
  let l := T*S.laneBits
  let b := virtualBits addr n-l
  let L := BlockProgram.layout B base (initialPositions addr n) T
  let bits : RAMSystem (virtualBits addr n) → ℕ := ramFieldBits (virtualBucket n) (wordBits addr n)
  let mem := after incoming (eventLog (cursorStartupLogs boot pub addr n base incoming A.initial.length A.block.length A.size))
  StartupResult boot A.plan terminal pub addr n base incoming clk ∧
    ∃ hD : 1 < b+l, let X := cursorState (cursorCoordinateLabels b l) hD hd bits
      ∃ initial : InitialInterval B base (initialPositions addr n) T (sourceCap pub clk) (BlockClock.small B addr n)
        b l (initialWidth addr n) pub mem,
        Boundary (CurrentResident.resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n
          (cursorFrame L (S.degreeExponent 0) b l (initialWidth addr n))) pub
          (levelWords L : Word (wordBits addr n)) (directoryRows L) 4 [] X initial.interval.segment.memory ∧
        RAMBuckets.cost Report.probes initial.interval.source.logs ≤ initialRate B*(initialPositions addr n+1) ∧
        BlockClock.small B addr n+3 ≤ sourceCap pub clk ∧
        sourceCap pub clk+24 = CompressedPair.clockAt pub clk CompressedPair.Stage.online

attribute [local semireducible] InitialTransferred.bootstrap BlockProgram.script BlockProgram.layout

set_option exponentiation.threshold 10000 in
theorem eventually_initial_live_uniform (c : Constants) (terminal : PairTable) (p q addr : ℕ) {H : ℕ → ℕ}
    (hq : 0 < q) (haddr : 1 ≤ addr) (hθ : (p : ℝ)/q ≤ 1) (lanes : S.laneBits ≤ addr) (hH : PolynomiallyBounded H) :
    ∃ hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0), ∀ᶠ n : ℕ in atTop, ∀ {R : Type v} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      ∀ (lit : LiteralPrefix) (incoming : Memory (wordBits addr n)) (G : PairStages.Group),
        let g := paperGeometry addr H n
        let pub := Pieces.word g lit ∘ StageOperands.pair c
        let base := (LiveProgram.Layout.pairWorkspace c).eval g
        G.clock = n^10000 → incoming (PairTag.address pub).val = 0 →
          InitialLive B f hf p q addr n base (G.clockAt LiveProgram.Stage.pair) terminal pub incoming hd := by
  let A := BlockProgram.script B
  let boot := InitialTransferred.bootstrap B p q
  let base n := (LiveProgram.Layout.pairWorkspace c).eval (paperGeometry addr H n)
  have hb : PolynomiallyBounded base := startup_workspace_polynomial c haddr hH
  obtain ⟨hd,run⟩ := eventually_initial_uniform B p q addr hq haddr hθ lanes hb
  have enough : 7 ≤ boot.shape.arity := (by decide : 7 ≤ 11).trans (InitialTransferred.arity B)
  obtain ⟨K,start⟩ := eventually_physical_startup c boot A.plan terminal addr haddr hH hq
    (InitialTransferred.phases_pos B) hθ lanes rfl enough (by change 30 ≤ 54; decide)
  refine ⟨hd,?_⟩
  filter_upwards [run,start,eventually_startup_inputs c haddr hH,eventually_clocks B addr haddr,
    eventually_polylog_le K 1,eventually_ge_atTop 128] with n initialized startup data clocks length hn
  intro R _ f hf lit incoming G g pub address time tag
  let clk := G.clockAt LiveProgram.Stage.pair
  have low := CompressedPair.private_clock_room G hn time
  have lower : K*(n.log2+1) ≤ clk :=
    (by simpa only [pow_one] using length : K*(n.log2+1) ≤ n).trans
      ((Nat.le_self_pow (by decide : 9999 ≠ 0) n).trans (le_trans (Nat.le_add_right _ _) low))
  have ready := startup lit incoming clk tag lower
  obtain ⟨ws,len,addrEq,tagLt⟩ := data lit
  obtain ⟨initialBound,control,available⟩ := clocks
  obtain ⟨slack,joinedClock⟩ := available G pub time
  obtain ⟨hD,initial,boundary,cost⟩ := initialized f hf pub ws len addrEq (tagLt.trans_le ws.le) incoming terminal clk
    (sourceCap pub clk) (BlockClock.small B addr n) ready initialBound ((Nat.le_add_right _ _).trans slack) control
  exact ⟨ready,hD,initial,boundary,cost,slack,joinedClock⟩

set_option exponentiation.threshold 10000 in
/-- The live initialization specialized to fixed coefficients. -/
theorem eventually_initial_live (c : Constants) (terminal : PairTable) (p q addr : ℕ) {H : ℕ → ℕ}
    (hq : 0 < q) (haddr : 1 ≤ addr) (hθ : (p : ℝ)/q ≤ 1) (lanes : S.laneBits ≤ addr) (hH : PolynomiallyBounded H) :
    ∃ hd : 2+(2^(S.degreeExponent 0)-2) = 2^(S.degreeExponent 0), ∀ᶠ n : ℕ in atTop,
      ∀ (lit : LiteralPrefix) (incoming : Memory (wordBits addr n)) (G : PairStages.Group),
        let g := paperGeometry addr H n
        let pub := Pieces.word g lit ∘ StageOperands.pair c
        let base := (LiveProgram.Layout.pairWorkspace c).eval g
        G.clock = n^10000 → incoming (PairTag.address pub).val = 0 →
          InitialLive B f hf p q addr n base (G.clockAt LiveProgram.Stage.pair) terminal pub incoming hd := by
  obtain ⟨hd,allModels⟩ := eventually_initial_live_uniform B c terminal p q addr hq haddr hθ lanes hH
  exact ⟨hd,allModels.mono fun _ run => run f hf⟩

end CompressorRecords.ScheduledTrace

end

end VPVNP
end Computability
end OAI
