import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoom
import OAI.Computability.BorderVNP.DiagonalCubeStartupWorkspace

/-! # Fitting the signed arena from the actual startup fields and geometry packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins VPVNP
open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena BorderVNP.Cube
open TeamContraction.ProcessorSlots
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {F : Type*} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ}

/-- The real length-only startup, physical processor slots, and public
geometry packet bound give the signed allocation directly. The final
address bound and the common scalar ceiling precede every chart and
terminal execution. -/
theorem JointSchedule.eventually_signed_from_startup {K : Type*} [Field K] (cube : FixedCube K)
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
      ∀ (dir : Directory.Layout) (len copied slots profile program outputs codeWidth : ℕ),
        (len:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ) → copied ≤ r → 0<slots → r*literal s.α n ≤ slots →
        slots ≤ r*n → dir.teams=R → dir.processors=r → dir.entries=bundles → dir.fields≤2 →
        dir.block=blockWidth slots V → dir.literal=literal s.α n → 1≤codeWidth →
        GeometryAdviceRate.packetWords program profile outputs codeWidth*W ≤ r*width n (95/100:ℝ) →
        let initial : StartupArena := ⟨R,r,literal s.α n,b.physical.link n,len,copied⟩
        let base := GeometryAdvice.Allocation.stop (initial.next+7*dir.candidates) profile program outputs codeWidth W
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
  obtain ⟨C,power,physical⟩ := b.eventually_signed_physical_room (aux:=aux) (q:=q) cube f hf c k headerFactor
  refine ⟨C,power,?_⟩
  filter_upwards [physical,b.eventually_cube_startup_workspace cube] with n selected workspace
  intro l eqn r R W X symbols start V T cells cables bundles axes marked body lim pin seed
    dir len copied slots profile program outputs codeWidth lenFit copiedFit positive enough slotBound
    teams processors entries fields block literals widthFit packet initial base p arena id dirs size ord
    common chart prime alg reader charge
  have ready := workspace dir len copied slots profile program outputs codeWidth lenFit copiedFit positive
    enough slotBound teams processors entries fields block literals widthFit packet
  exact selected l eqn seed dir initial.next profile program outputs codeWidth ready.2.1 id dirs chart reader charge

end Diagonal

end BorderVNP
end Computability
end OAI
