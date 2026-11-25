import OAI.LinearAlgebra.SpectralBooks.VNP.WeightedClosing
import OAI.LinearAlgebra.SpectralBooks.SignedQueries
import OAI.LinearAlgebra.SpectralBooks.ProfileShortening

/-! # Reduction of the border stretch bound to effective pins and the programmed contraction

The two remaining constructions have distinct quantifiers. Descent and residue extraction supply
one bounded entry computation from membership in a parse-map image closure. Shortening has to
simulate every such computation with any specified distinguished index. The program in this
second assertion receives the index and entry routine, without access to the residue vector.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace VNP

open MvPolynomial Filter Matrix

noncomputable section

abbrev Query (n : ℕ) := Fin n → Bool
abbrev Parameter (n s : ℕ) := ParseParameter n (Fin (3*s+3)) (Fin n × Bool)

/-- The full degree-`n` coefficient vector belongs to the closure of the homogeneous parse
map. The descent construction uses all these coefficients in its finite slice equations. -/
def InParseBoundary (k : Type*) [Field k] (n s : ℕ) : Prop :=
  degreeCoefficientVector n (signedWitnessPolynomial (AlgebraicClosure k) n) ∈
    zeroLocus (AlgebraicClosure k) (vanishingIdeal (AlgebraicClosure k)
      (parseImage (AlgebraicClosure k) (Fin n × Bool) n s))

/-- Source and target for the polynomial substitution before any geometric wiring changes. -/
def queryPolynomial (E : Type*) [Field E] {n : ℕ} (s : ℕ) (x : Query n) :
    MvPolynomial (Parameter n s) E := map (Int.castRingHom E) (signedQueryCoordinate s x)

variable {k E : Type*} [Field k] [Field E] {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) E]
    {σ ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single signed counting machine and advice string compute every requested prime-field
entry. The address encoding and the bit and step budgets are fixed before a table is supplied.
The `0,1` machines of the residue-pins lemma are instances of these signed computations. -/
def EntryRoutine (address : (σ →₀ ℕ) → E → ι → ι → List Bool) (L bits steps : ℕ)
    (W : (σ →₀ ℕ) → E →ₗ[ZMod p] Matrix ι ι (ZMod p)) : Prop :=
  ∃ (program : SignedMachine.Program) (advice : List Bool), ProgramCode.WellFormed program ∧
    (ProgramCode.encode program).length + advice.length ≤ bits ∧
    ∀ μ : σ →₀ ℕ, μ.degree ≤ L → ∀ a i j,
      W μ a i j = (SignedMachine.pathSum program
        (ProgramCode.encode program ++ advice ++ address μ a i j) steps : ZMod p)

variable (E) (n s : ℕ) (ι)

/-- The arithmetic assertion furnished by the effective residue-pins construction for the
integral parse coordinates. The distinguished nonzero index is chosen only after the vector. -/
def HasEffectiveQueryPins
    (address : (Parameter n s →₀ ℕ) → E → ι → ι → List Bool) (L bits steps : ℕ) : Prop :=
  ∃ (W : (Parameter n s →₀ ℕ) → E →ₗ[ZMod p] Matrix ι ι (ZMod p)) (Ω : ι → ZMod p),
    Ω ≠ 0 ∧ EntryRoutine address L bits steps W ∧
    ∀ G : MvPolynomial (Query n) (ZMod p), (aeval (queryPolynomial E s) G).totalDegree ≤ L →
      pinMatrix W (aeval (queryPolynomial E s) G) *ᵥ Ω =
        eval (fun x => (signedWitness x : ZMod p)) G • Ω

/-- The weighted program assertion for all entry routines within the fixed budgets.
`assign i` labels precisely the retained terms in the expanded contraction for row `i`. -/
def CanProgramWeightedContraction
    (address : (Parameter n s →₀ ℕ) → E → ι → ι → List Bool) (L bits steps : ℕ) : Prop :=
  ∀ (W : (Parameter n s →₀ ℕ) → E →ₗ[ZMod p] Matrix ι ι (ZMod p)),
    EntryRoutine address L bits steps W → ∀ H : ι,
    ∃ (G : ι → MvPolynomial (Query n) (ZMod p)) (count : ι → ℕ)
      (μ : (i : ι) → Fin (count i) → Parameter n s →₀ ℕ) (a : (i : ι) → Fin (count i) → E),
      (∀ i, (aeval (queryPolynomial E s) (G i)).totalDegree ≤ L) ∧
      (∀ i, aeval (queryPolynomial E s) (G i) = ∑ e, monomial (μ i e) (a i e)) ∧
      ∀ j, eval (fun x => (signedWitness x : ZMod p)) (G j) = (if j = H then 1 else 0) +
        ∑ i, ∑ e, W (μ i e) (a i e) i j

/-- One effective residue readout rules out the corresponding universal programmed contraction. -/
theorem effectivePins_exclude_programmedContraction
    (address : (Parameter n s →₀ ℕ) → E → ι → ι → List Bool) (L bits steps : ℕ)
    (hpins : HasEffectiveQueryPins (p := p) E ι n s address L bits steps) :
    ¬ CanProgramWeightedContraction (p := p) E ι n s address L bits steps := by
  classical
  intro hprogram
  obtain ⟨W, Ω, hn, hentry, heigen⟩ := hpins
  obtain ⟨H, hH⟩ : ∃ i, Ω i ≠ 0 := by simpa [funext_iff] using hn
  obtain ⟨G, count, μ, a, hdeg, hexp, hpr⟩ := hprogram W hentry H
  exact boundary_program_impossible W Ω H hH (queryPolynomial E s) _ G L hdeg heigen _ μ a hexp hpr

/-- When descent yields effective pins from the image closure and shortening supplies the
program, the size bound fails for the actual signed witness at this length. -/
theorem signedWitness_size_gt_of_programmed_pins
    (address : (Parameter n s →₀ ℕ) → E → ι → ι → List Bool) (L bits steps : ℕ) (hn : 0 < n)
    (hdescent : InParseBoundary k n s → HasEffectiveQueryPins (p := p) E ι n s address L bits steps)
    (hprogram : CanProgramWeightedContraction (p := p) E ι n s address L bits steps) :
    s < degreeBorderSize n (signedWitnessPolynomial k n) := by
  by_contra! hs
  exact effectivePins_exclude_programmedContraction E ι n s address L bits steps
    (hdescent (signedWitness_mem_parseClosure k hn hs)) hprogram

/-- Excluding the parse boundary at the manuscript's integer budget gives the real
stretched-exponential degree-component lower bound at every sufficiently large length. -/
theorem signedWitnessHardness_of_excluded_parseBoundaries (k : Type*) [Field k] (ε : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, ¬ InParseBoundary k n ⌊(2 : ℝ) ^ ((n : ℝ) ^ ε)⌋₊) :
    SignedWitnessHardness k ε := by
  filter_upwards [h, eventually_gt_atTop 0] with n h hn
  change _ ≤ (degreeBorderSize n (signedWitnessPolynomial k n) : ℝ)
  apply le_of_lt
  apply (Nat.floor_lt (by positivity)).mp
  apply lt_of_not_ge
  intro hs
  exact h (signedWitness_mem_parseClosure k hn hs)

/-- A fixed finite encoding of the reduction prime, extension-field coefficients, pin indices,
and machine resource limits. The encoding is shared by descent and the programmed simulation. -/
structure PinLayout (n s : ℕ) where
  prime : ℕ
  prime_fact : Fact prime.Prime
  extensionDegree : ℕ
  degree_pos : 0 < extensionDegree
  indices : ℕ
  degreeLimit : ℕ
  adviceBits : ℕ
  steps : ℕ
  address : (Parameter n s →₀ ℕ) → @GaloisField prime prime_fact extensionDegree →
    Fin indices → Fin indices → List Bool

namespace PinLayout

variable {n s : ℕ}

def hasPins (P : PinLayout n s) : Prop :=
  letI := P.prime_fact
  HasEffectiveQueryPins (p := P.prime) (GaloisField P.prime P.extensionDegree)
    (Fin P.indices) n s P.address P.degreeLimit P.adviceBits P.steps

def canProgram (P : PinLayout n s) : Prop :=
  letI := P.prime_fact
  CanProgramWeightedContraction (p := P.prime) (GaloisField P.prime P.extensionDegree)
    (Fin P.indices) n s P.address P.degreeLimit P.adviceBits P.steps

theorem incompatible (P : PinLayout n s) (hpins : P.hasPins) : ¬ P.canProgram := by
  let := P.prime_fact
  exact effectivePins_exclude_programmedContraction _ _ n s _ _ _ _ hpins

/-- Positive characteristic retains the original prime. In characteristic zero a different
reduction prime is allowed at each input length. -/
def carriesReducedBoundary (P : PinLayout n s) (k : Type*) [Field k] : Prop :=
  letI := P.prime_fact
  (ringChar k = 0 ∨ P.prime = ringChar k) ∧ InParseBoundary (ZMod P.prime) n s

end PinLayout

/-- The integer size cutoff in the border-stretch contradiction. -/
noncomputable def stretchBudget (ε : ℝ) (n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((n : ℝ) ^ ε)⌋₊

/-- Row simulation from the shortening, for every acceptable pin layout and every entry
routine fitting that layout. `allowed` specifies the resource bounds and the reductions of the
fixed gadget data that the simulation can use. -/
def WeightedProgramSimulation (ε : ℝ)
    (allowed : ∀ n, Set (PinLayout n (stretchBudget ε n))) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ P ∈ allowed n, P.canProgram

/-- Sections 9 and 10 must supply a common admissible prime, a reduced parse boundary, and an
effective table at each sufficiently large length satisfying the small-border hypothesis. -/
def EffectivePrimeDescent (k : Type*) [Field k] (ε : ℝ)
    (allowed : ∀ n, Set (PinLayout n (stretchBudget ε n))) : Prop :=
  ∀ᶠ n : ℕ in atTop, InParseBoundary k n (stretchBudget ε n) →
    ∃ P ∈ allowed n, P.carriesReducedBoundary k ∧ P.hasPins

/-- The analytic and algebraic constructions exclude every sufficiently large length whose
signed witness has border size at most the integer cutoff. -/
theorem signedWitnessHardness_of_prime_descent_and_simulation (k : Type*) [Field k] {ε : ℝ}
    {allowed : ∀ n, Set (PinLayout n (stretchBudget ε n))}
    (simulation : WeightedProgramSimulation ε allowed) (descent : EffectivePrimeDescent k ε allowed) :
    SignedWitnessHardness k ε := by
  apply signedWitnessHardness_of_excluded_parseBoundaries
  filter_upwards [simulation, descent] with n hsim hdesc
  intro hsmall
  obtain ⟨P, hP, _, hpin⟩ := hdesc hsmall
  exact P.incompatible hpin (hsim P hP)

/-- The profiled shortening and its fixed format are chosen before the exponent and admissible
resource bounds. The prime and advice may vary at each length. The two remaining source inputs
are weighted program simulation and effective prime descent on those same bounds. -/
theorem borderStretch_of_simulation_and_descent (k : Type*) [Field k] (D : ℕ) (hD : 2 ≤ D)
    (shortening : Crossing.HasProfileShortening k D)
    (constructions : 2 ≤ D → Crossing.HasProfileShortening k D →
      ∃ ε : ℝ, 0 < ε ∧ ∃ allowed : ∀ n, Set (PinLayout n (stretchBudget ε n)),
        WeightedProgramSimulation ε allowed ∧ EffectivePrimeDescent k ε allowed) :
    ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness k ε := by
  obtain ⟨ε, hε, _, hs, hd⟩ := constructions hD shortening
  exact ⟨ε, hε, signedWitnessHardness_of_prime_descent_and_simulation k hs hd⟩

end
end VNP

end SpectralBooks
end LinearAlgebra
end OAI
