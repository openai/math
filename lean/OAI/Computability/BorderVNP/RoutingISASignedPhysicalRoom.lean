import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomRate
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReader
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomSeed

/-! # The complete selected signed-task address space on the joint diagonal schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins VPVNP
open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena BorderVNP.Cube
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {F : Type*} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ}

/-- A single cutoff precedes the choice of the actual chart, its reader
board, every owned cell, and every terminal history. It fits the complete
signed allocation selected from the physical seed and public geometry.
The input ceiling on the preceding geometry is its allocated high-water
address, as supplied by the selected cover workspace theorem. -/
theorem JointSchedule.eventually_signed_physical_room {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{u} s (E+1) dlog Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k headerFactor : ℕ) :
    ∃ C power : ℕ, ∀ᶠ n : ℕ in atTop, ∀ l, n=l+1 →
      let r := stretch b.ρ n
      let R := b.physical.teamsPred n+1
      let W := b.physical.word n
      let X := R*exterior ((s.τ:ℝ)/5) r n
      let symbols := Cube.alphabet s.α n
      let start := CoverScale.initialDepth (Epoch.Cube D) r n
      let V := CoverScale.sites (Epoch.Cube D) start
      let T := epochs s.τ n
      let cells := CoverScale.sites (Epoch.Cube D) (EnrichedOuter.depth S start T)
      let cables := (boundary S start T).edges+4*(R*V)
      let bundles := (epochCopies S)^T*V
      let axes := Fintype.card (Epoch.Cube D)
      let marked := DeckGrid.seedSiteCapacity n r axes (start-1)
      let body := BottomGridBank.bodyBudget (DeckGrid.seedBoxCapacity n r axes (start-1) (Fintype.card (DeckGrid.Direction axes)))
      let lim := f (adviceScale b.σ b.ρ n)
      let pin := lim+6
      Nonempty (SeedPlan S n r (start-1) T (width n s.α) headerFactor Q) →
      ∀ (dir : Directory.Layout) (next profile program outputs codeWidth : ℕ),
        let base := GeometryAdvice.Allocation.stop (next+7*dir.candidates) profile program outputs codeWidth W
        base≤2*r*n →
        let p := selectedSizes base symbols X cells cables dir.candidates R r n profile
        let arena := p.selected cube.pred cube.b cube.h cube.copies cube.width
        ∀ (id : TableEntry arena.n arena.b arena.h arena.K arena.s → ℕ) (geometry : GeometryDirectories)
          {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
          {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
          [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
          (reader : ChosenReader chart R r W W W pin),
          reader.charge≤c*(lim+1)^k →
          let par := pairedTableParameters (l+1) size
          let expBits := Nat.clog 2 (r*(2*l+1)+1)
          let labels := Fintype.card (G.Entry ⊕ ι)
          let query := Fintype.card (Board.Physical par pin W (G.Entry ⊕ ι))
          let guesses := Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
          let params := physicalParameters arena geometry n bundles marked par expBits labels W
            (headerFactor*logWidth r n) body
          let task : SignedTaskArena.Layout := ⟨arena,id,params⟩
          let envelope := C*(r*n+1)^power
          p.Le envelope ∧ task.ScalarRoom W query guesses reader.gates envelope ∧
            task.endAddress W query guesses reader.gates < 2^W := by
  obtain ⟨C,power,parameters⟩ := parameters_polynomial cube.pred cube.b cube.h cube.copies cube.width
  refine ⟨C,power,?_⟩
  filter_upwards [b.eventually_signed_source_sizes cube,b.eventually_reader_physical_room (aux:=aux) (q:=q) f hf c k,
    eventually_signed_word cube.pred cube.b cube.h cube.copies cube.width C power E,eventually_ge_atTop 1]
    with n primitive readers word hn
  intro l eqn r R W X symbols start V T cells cables bundles axes marked body lim pin seed dir next profile
    program outputs codeWidth base baseFits p arena id geo size ord common chart prime alg reader charge
    par expBits labels query guesses params task envelope
  have hr := stretch_one b.ρ n
  have data := primitive dir next profile program outputs codeWidth baseFits
  have board := (readers l eqn chart reader charge).1
  have markedRoom := mark_room_of_seed s hn hr seed
  have nz : n+1≤r*n+1 := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hr) 1
  obtain ⟨cubeFit,allFit⟩ := parameters n (r*n+1) p (Nat.succ_pos _) nz data.1 id geo bundles marked par
    expBits labels W (headerFactor*logWidth r n) body query guesses reader.gates data.2 markedRoom
    board.powerSlots board.parameters board.gadgets board.word board.queryBits board.choiceBits board.gates
  have fitted := word r hr p task W query guesses reader.gates cubeFit rfl allFit
  have wordSize : W=logWidth r n^(E+2) := (b.sizes hn).2.2.1
  exact ⟨cubeFit,allFit,fitted.trans_eq (congrArg (fun k : ℕ => 2^k) wordSize.symm)⟩

end Diagonal

end BorderVNP
end Computability
end OAI
