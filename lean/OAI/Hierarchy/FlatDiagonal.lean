import OAI.Hierarchy.FlatFieldTransfer
import OAI.Hierarchy.ExcludedCubeExpanders
import OAI.Hierarchy.GridProgrammed
import OAI.Hierarchy.CollapseDescent
import OAI.Hierarchy.TaggedWidthLimit
import OAI.Hierarchy.TaggedApproximation

namespace OAI
/-! # From the protocol, descent, lens and trace theorems to every spectral flat

The hypotheses are separated at the paper's mathematical interfaces. In
particular the full price system and addressed tick table are the same in
the two uses of the programmed grid. -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks

noncomputable section
open scoped Classical

/-- Selected physical experiments can depend on the prime and flat
dimension. Their integer sizes, controller input and replacement network are
part of the experiment before the actual controller is encoded. -/
structure FlatExperiment (F : Type) [Field F] (d : ℕ) where
  grid : UniversalGrid.Grid F d
  place : GridDiagonal.Ends (Fin grid.rails) → EuclideanSpace ℝ (Fin d)
  prices : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d))

def FlatExperiment.strict {F : Type} [Field F] {d : ℕ} (t : FlatExperiment F d) : Prop :=
  ∀ code, t.grid.exactGrid code - t.grid.accelerated code = 0 ∨
    t.prices.price (GridDiagonal.raw (t.grid.exactGrid code - t.grid.accelerated code)) t.place <
      t.prices.price (GridDiagonal.raw (GridDiagonal.identity F)) t.place

/-- A maximal finite flat gives rise to cheap exposed tags, pointwise collapse
for arbitrary ticks, and a physical experiment with uniformly cheaper error.
Trace distribution and the honest program apply separately to every
eligible experiment. Field transfer is the final, independent step. -/
theorem all_flats_of_routing_descent_and_grid
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k →
      HasSpectralFlat (ZMod p) k → ¬HasSpectralFlat (ZMod p) (k+1) →
      NonlinearExpanders.SpectralFamily (ZMod p) →
      ∀ r : ℝ, 0 < r → Tagged.Feasible (ZMod p) k 1 r)
    (descent : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k →
      NonlinearExpanders.SpectralFamily (ZMod p) →
      (∀ r : ℝ, 0 < r → Tagged.Feasible (ZMod p) k 1 r) →
      Catalyst.HasPointwiseCollapse (ZMod p) k)
    (Experiment : ℕ → ℕ → Type)
    (build : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Experiment p k → FlatExperiment (ZMod p) k)
    (lens : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k →
      HasSpectralFlat (ZMod p) k → NonlinearExpanders.SpectralFamily (ZMod p) →
      Catalyst.HasPointwiseCollapse (ZMod p) k → ∃ t, (build p k t).strict)
    (distribution : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k →
      NonlinearExpanders.SpectralFamily (ZMod p) → ∀ t, let G := (build p k t).grid
        ∃ code, Nonempty (G.Distributed code))
    (F : Type*) [Field F] (d : ℕ) : HasSpectralFlat F d := by
  apply HasSpectralFlat.of_prime_fields _ F
  intro p _
  by_contra missing
  obtain ⟨k, hk, _, flat, maxdim⟩ := HasSpectralFlat.maximal_of_missing missing
  have miss : ¬HasSpectralFlat (ZMod p) (k+1) := fun higher =>
    Nat.not_succ_le_self _ (maxdim _ higher)
  have ports := NonlinearExpanders.family_of_missing NonlinearExpanders.excluded_cube (by omega : 2 ≤ k+1) miss
  have tag := width p k hk flat miss ports
  have small := descent p k hk ports tag
  obtain ⟨t, gap⟩ := lens p k hk flat ports small
  obtain ⟨code, witness⟩ := distribution p k hk ports t
  exact (build p k t).grid.excludes (build p k t).prices (build p k t).place gap code witness.some

open Filter ThreeFlat

namespace TickSelection

variable {F : Type} [Field F] [Fintype F] {k A w : ℕ} {Q : ℕ→ℕ} {D : ℕ→ℝ}
variable (v : TickSelection F k A w Q D)

def network := UniversalTick.tick v.fieldRoom v.tickFit.width v.tickFit.labels 0 0
  v.tickFit.header v.tickFit.time (GridDescription.capacity w) (GridDescription.capacity w)

/-- Compiler and trace correctness on the one tick and replacement already
chosen independent of the controller, at their actual rail and selector sizes. -/
def HasDistribution : Prop :=
  let a := GridScale.overhead Q D w
  let e := GridScale.external k a (GridScale.pairs A w v.copies)
  let n := GridScale.side a-1
  ∃ (dir : Fin e → Fin k) (control : UniversalGrid.Bits (w^2) →
    UniversalGrid.Bits (GridScale.selector k w a) →
    Option (GridThrough.Setting v.replacement n e dir))
    (code : UniversalGrid.Bits (w^2)),
      Nonempty ((GridThrough.grid v.network v.replacement dir control).Distributed code)

theorem impossible (env : GridScale.Envelopes Q D) (hk : 0<k)
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) :
    ∀ᶠ w : ℕ in atTop, ∀ v : TickSelection F k A w Q D, ¬v.HasDistribution := by
  filter_upwards [GridThrough.strict env A hk P] with w lens
  rintro v ⟨dir,control,code,⟨real⟩⟩
  exact (GridThrough.grid v.network v.replacement dir control).excludes P _
    (lens v.copies v.copies_pos v.copies_le v.network v.replacement dir v.gap control) code real

end TickSelection

/-- On any cofinal sequence of word sizes the compiler may build on a
replacement chosen ahead of its own executable. Its cost exponent is
quantified before the saving exponent. -/
def GridTraceCompiler (F : Type) [Field F] [Fintype F] (k : ℕ) : Prop :=
  ∃ c : ℕ, ∀ A>c, ∀ Q D, GridScale.Envelopes Q D →
    ∃ᶠ w : ℕ in atTop, ∀ v : TickSelection F k A w Q D, v.HasDistribution

/-- The three remaining constructive inputs are the tagged width constructions,
the bounded oracle layer compiler, and distribution of its native grid trace.
The nonlinear expander, universal tick choice, lens and characteristic transfer
are explicit applications to the same prime and the same maximal dimension. -/
theorem all_flats_of_native_constructions
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
      ¬ HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
        Tagged.RadixBound (ZMod p) k ∧ Tagged.WidthReductions (ZMod p) k)
    (layer : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
    (compiler : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k →
      NonlinearExpanders.SpectralFamily (ZMod p) → GridTraceCompiler (ZMod p) k)
    (F : Type*) [Field F] (d : ℕ) : HasSpectralFlat F d := by
  apply HasSpectralFlat.of_prime_fields _ F
  intro p _
  by_contra missing
  obtain ⟨k,hk,_,hflat,hmax⟩ := HasSpectralFlat.maximal_of_missing missing
  have miss : ¬ HasSpectralFlat (ZMod p) (k+1) := fun next => Nat.not_succ_le_self _ (hmax _ next)
  have exp := NonlinearExpanders.family_of_missing NonlinearExpanders.excluded_cube (by omega : 2≤k+1) miss
  obtain ⟨radix,reduce⟩ := width p k hk hflat miss exp
  have Z := Tagged.profile_zero_of_reductions radix reduce
  have cheap (r : ℝ) (hr : 0<r) : Tagged.Feasible (ZMod p) k 1 r :=
    Tagged.feasible_of_profile_lt (Tagged.Exact.rates_nonempty _ _ 1) (by simpa only [Z] using hr)
  have small : Catalyst.HasPointwiseCollapse (ZMod p) k := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    exact CollapseOracle.pointwise_collapse m (layer p) cheap
  let : NeZero k := ⟨by omega⟩
  obtain ⟨c,run⟩ := compiler p k hk exp
  obtain ⟨A,hA,Q,D,env,chosen⟩ := choose_tick small c
  have h := (run A hA Q D env).and_eventually (chosen.and
    (TickSelection.impossible (A:=A) env (by omega : 0<k) hflat.some))
  obtain ⟨w,distribute,⟨v⟩,forbidden⟩ := h.exists
  exact forbidden v (distribute v)


end
end Hierarchy

end OAI
