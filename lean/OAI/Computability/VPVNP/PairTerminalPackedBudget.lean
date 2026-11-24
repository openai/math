import OAI.Computability.VPVNP.PairTerminalLayout
import OAI.Computability.VPVNP.PairTraversalControllerOrdinal
import OAI.Computability.VPVNP.PairTerminalSelectedHeaders
import OAI.Computability.VPVNP.PairSimulationTerminalProgram
import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.LiveCompressedPairHandoff
import OAI.Computability.VPVNP.LiveProgramCompressedPairPaths

/-!
# Resource bounds for the packed physical terminal directory

The native startup reserves the actual number of calendar rows. The first DFS
address is the end of that packed directory. The fixed instruction table reads
its dynamic dimensions from memory and uses the same compiled layout constants
at every input length. The room here includes the private map staging region
after all cursor verifier stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open BurstRAM PrivateRAM Compression CursorNetwork CursorBounds CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles Filter

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

private theorem calculation_congr (F G : Shape) (limit : ℕ)
    (arity : F.arity = G.arity) (scalars : F.scalarFields = G.scalarFields) :
    TerminalBootstrap.calculation F limit = TerminalBootstrap.calculation G limit := by
  rcases F with ⟨a,i,l,s,f,t,d,k⟩
  rcases G with ⟨b,j,m,v,g,u,e,n⟩
  change a = b at arity
  change f = g at scalars
  subst b
  subst g
  rfl

private theorem bank_congr (F G : Shape) (limit : ℕ)
    (segments : VertexImage.Part → VertexImage.Segment)
    (arity : F.arity = G.arity) (scalars : F.scalarFields = G.scalarFields) :
    TerminalProgram.workers F limit segments = TerminalProgram.workers G limit segments := by
  unfold TerminalProgram.workers TerminalBootstrap.table
  rw [calculation_congr F G limit arity scalars]

/-- The bootstrap has a fixed source instruction count independent of the
number of rows in the chronological directory. -/
theorem packed_bootCost (B : S.Templates) (base positions blocks : ℕ) :
    TerminalBootstrap.cost (BlockProgram.layout B base positions blocks).shape B.recordLimit =
      TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit := by
  exact congrArg (fun d => d.recipe.code.length)
    (calculation_congr (BlockProgram.layout B base positions blocks).shape
      (BlockProgram.allocationShape B) B.recordLimit rfl rfl)

/-- The initial row count and the per-level directory length vary, while the
code of the terminal worker bank is the fixed code chosen with the templates. -/
theorem packed_workers (B : S.Templates) (base positions blocks : ℕ)
    (segments : VertexImage.Part → VertexImage.Segment) :
    TerminalProgram.workers (BlockProgram.layout B base positions blocks).shape
      B.recordLimit segments =
      TerminalProgram.workers (BlockProgram.allocationShape B) B.recordLimit segments :=
  bank_congr _ _ _ _ rfl rfl

/-- Dispatch of the live pair and its inner terminal phase consumes forty-one
units of the enclosing processor clock before the worker's private cut. -/
theorem pair_clock (G : LiveProgram.PairStages.Group) :
    LiveProgram.CompressedPair.clockAt (LiveProgram.PairStages.Group.CompressedPaths.publicWords G)
      (LiveProgram.PairStages.Group.CompressedPaths.fuel G)
      LiveProgram.CompressedPair.Stage.terminal =
      G.clock - 41 := by
  change (G.clock-14)-5-22 = G.clock-41
  omega

set_option exponentiation.threshold 10000 in
/-- The live pair clock supplies all fixed controller and linker margins. -/
theorem eventually_pair_clock (K : ℕ) : ∀ᶠ n : ℕ in atTop,
    ∀ G : LiveProgram.PairStages.Group, n^10000 ≤ G.clock →
      K ≤ LiveProgram.CompressedPair.clockAt
        (LiveProgram.PairStages.Group.CompressedPaths.publicWords G)
        (LiveProgram.PairStages.Group.CompressedPaths.fuel G)
      LiveProgram.CompressedPair.Stage.terminal := by
  filter_upwards [eventually_ge_atTop (K+41)] with n hn
  intro G hg
  rw [pair_clock]
  have h := Nat.le_self_pow (by decide : 10000 ≠ 0) n
  omega

/-- Simultaneous numerical room for the actual branch. The term choice,
field assignment, register contents and optional map work are outside the
choice of the length threshold. -/
theorem eventually_packedFit (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {start : ℕ → ℕ} (hstart : PolynomiallyBounded start)
    (ports : ℕ) (extra : ℕ → ℕ) (hextra : PolynomiallyBounded extra) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let w := wordBits b n
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f hf T hT X
      let L := BlockProgram.layout B (start n) (initialPositions b n) T
      let H := headerBase (start n) (addressBits b n)
      ∀ z : E.Choices,
        let Y := E.finalState z
        let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
        let tags := selected B f hf T hT X z
        let R := privateRegions (slotDegree S) n (endAddress L+rows) (Fintype.card B.Entry)
        endAddress L + 2*rows + Y.totalWidth < H ∧ H+32 ≤ 2^w ∧
          R.histBase + R.histWords + 12 ≤ R.cacheBase ∧
          R.stackBase + ports*n^40 + extra n < 2^w ∧
          2*tags.length*(X.positions+1) < 2^w := by
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [eventually_fitWithReserve B u (BlockProgram.allocationShape B) b hb hstart
    ports extra hextra, TraversalControllerOrdinal.eventually_selected_fit B u b hb'] with n h hO
  intro base lanes labels hD hT A _ f hf w X T E L H z Y rows tags R
  let upper := cursorLayout (BlockProgram.allocationShape B) b S.steps u.θ (start n) n
  let U := privateRegions (slotDegree S) n (endAddress upper+rows) (Fintype.card B.Entry)
  have eqn := BlockProgram.allocation_end B (start n) (initialPositions b n) T
  change endAddress L ≤ endAddress upper at eqn
  have ⟨ext,head,hist,stack⟩ := h labels hD hT A f hf z
  change endAddress upper+2*rows+Y.totalWidth < H at ext
  change U.histBase + U.histWords + 12 ≤ U.cacheBase at hist
  change U.stackBase+ports*n^40+extra n < 2^w at stack
  have hlen : tags.length = (executeLevels B f hf T hT X z).length+1 := by
    simp only [tags,selected,List.length_cons,List.length_map]
  refine ⟨by omega,head,?_,?_,?_⟩
  · change R.histBase + Fintype.card B.Entry + 12 ≤ R.histBase + Fintype.card B.Entry + n^5
    change U.histBase + Fintype.card B.Entry + 12 ≤ U.histBase + Fintype.card B.Entry + n^5 at hist
    omega
  · apply lt_of_le_of_lt _ stack
    dsimp only [R,U,privateRegions,LeafArena.Regions.stackBase,LeafArena.Regions.cacheBase,
      LeafArena.Regions.histBase,NodeArguments.Arena.base]
    gcongr
  · rw [hlen]
    exact hO labels hD hT A f hf z

end PairSimulation.TerminalLayout

end VPVNP
end Computability
end OAI
