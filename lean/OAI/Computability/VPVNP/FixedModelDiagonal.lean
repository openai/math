import OAI.Computability.VPVNP.PairedEvaluatorContradiction
import OAI.Computability.VPVNP.LivePhysicalContractionRealized

/-!
# The per-length diagonal for a fixed joint model

The physical first-half counter vector stores production counts in parser order and
compressor counts after them. The midpoint advice reorders this vector into the label
coordinates of the joint equations. The same order is used in the evaluator's initial
configuration, its modular path count, and the weighted primed contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open JointLabelSystem LabelEvaluator CutSchedule ExponentTrace UniversalMachine
open LiveEvaluatorEncoding ChainAssignments BurstRAM BurstRAM.PrivateRAM
open scoped Classical

local instance diagonalPrimeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
/-- Enumerate the finite ground field in the local certificate. -/
noncomputable local instance diagonalGroundFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Use the slice embedding to give the ambient field its ground-field algebra structure. -/
noncomputable local instance diagonalGroundAlgebra (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra
/-- Decide equality of production labels in the physical counter order. -/
noncomputable local instance diagonalProductionDecEq (n c : ℕ) : DecidableEq (Production n c) := Classical.decEq _

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Number of counters in the first-half live cut, in physical parser order. -/
noncomputable abbrev denseCount (n c : ℕ) := FixedRows.productionCount n c + Fintype.card B.Entry

/-- The midpoint scatter turns a physical counter vector into an evaluator input. -/
noncomputable def formalExponents {n c : ℕ} (xs : Fin (B.denseCount n c) → ℕ) :
    Fin (B.compressorLabelCount c n) → ℕ := xs ∘ (FixedRows.labelOrder B.Entry n c).symm

private theorem denseExponent_lt {n c r : ℕ} (μ : PairNomination n c r) (ν : B.Entry → ℕ)
    (hν : ∀ v, ν v < 2^(2*r)) (j : Fin (B.denseCount n c)) :
    B.denseExponent (fun v => (μ v).val) ν j < 2^(2*r) := by
  obtain ⟨(a | a), rfl⟩ := finSumFinEquiv.surjective j
  · simp [denseExponent]
  · simpa [denseExponent] using hν ((Fintype.equivFin B.Entry).symm a)

/-- Every prefix of the `2^h` pairs fits in `Z` bits, including the last prefix. -/
private theorem prefix_lt {t h r Z : ℕ} (hZ : h+2*r ≤ Z) (inc : Fin (2^h) → Fin t → ℕ)
    (hb : ∀ i a, inc i a < 2^(2*r)) (i : Fin (2^h)) (a : Fin t) :
    partialSum inc i.succ a < 2^Z := by
  have hpre : partialSum inc i.succ a ≤ partialSum inc (Fin.last (2^h)) a := by
    unfold partialSum
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
  rw [prefix_last] at hpre
  calc
    _ ≤ ∑ j, inc j a := hpre
    _ < ∑ _ : Fin (2^h), 2^(2*r) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hb j a)
    _ = 2^(h+2*r) := by simp [pow_add]
    _ ≤ 2^Z := Nat.pow_le_pow_right (by decide) hZ

private theorem formalExponents_sum {I : Type*} [Fintype I] {n c : ℕ}
    (μ : I → Production n c → ℕ) (ν : I → B.Entry → ℕ) :
    B.formalExponents (fun j => ∑ i, B.denseExponent (μ i) (ν i) j) =
      fun j => ∑ i, joinAssignment (μ i) (ν i) j := by
  funext j
  apply Finset.sum_congr rfl
  intro i _
  rw [← B.denseExponent_labelOrder, Equiv.apply_symm_apply]

/-- The length-specific compiler data used in Proposition 9.1 and §14.3. `program` and `E`
are explicit parameters so an eventual construction can fix both tables before choosing `n`.
The processor realization is supplied separately to `false_of_processor`. -/
structure LocalCertificate {n c : ℕ} (hn : 2 ≤ n) {p : Nat.Primes}
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (h Δ a r e w Z radius : ℕ) (program : UniversalMachine.Program)
    (hf : ProcessorInput.Fits program n r (2^e) w) (E : UniversalMachine.Program)
    {pc regs pubs : ℕ} (D : Machine w pc regs pubs) (fuel : ℕ) (start : BurstRAM.Word w) where
  hw : 4 ≤ w
  hc : 2^r * 2^e < 2^w
  hR : 4*n ≤ 2^r
  hZ : h+2*r ≤ Z
  /-- The common advice bits distributed to all groups of the chain. -/
  advice : Bits a
  fit : 1 + B.denseCount n c * Z ≤ Δ
  layout : LiveEvaluatorTail.Layout E.extra radius w Δ
  /-- Finite paths for the given exterior, pair index and nominated production multiplicities. -/
  Path : Exterior h Δ → Fin (2^h) → PairNomination n c r → Type
  [pathFintype : ∀ ξ i μ, Fintype (Path ξ i μ)]
  /-- Multiplicity of each compressor label on the selected pair path. -/
  ν : ∀ ξ i μ, Path ξ i μ → B.Entry → ℕ
  hν : ∀ ξ i μ q v, ν ξ i μ q v < 2^(2*r)
  hpair : ∀ ξ i μ, (∑ q : Path ξ i μ, ∏ v, (B.compressorValues hn M v) ^ ν ξ i μ q v) =
    (GrammarDiagonal.multiplicity (⟨n-1, by omega⟩ : Fin n) (⟨0, pow_pos (by omega) _⟩ : Fin (n^(c+5)))
      (PairedChain.siteInput program hf advice ξ i) μ : M.algebra)
  /-- Initial scalar evaluator configuration for an exponent vector in formal label order. -/
  initial : (Fin (B.compressorLabelCount c n) → ℕ) → Config E.extra
  /-- Bounded encoding of the midpoint configuration for counters in physical order. -/
  init : (Fin (B.denseCount n c) → ℕ) → Code E.extra radius
  hi : ∀ xs, (init xs).toState = EvaluatorTail.canonical (initial (B.formalExponents xs))
  histories : ∀ xs, LiveEvaluatorTail.HistoriesFit E radius (2^h) (initial xs)
  htail : ∀ xs, (∀ j, xs j < 2^Z) → (paths E (2^h) (initial xs) : ZMod p.val) =
    (M.presentation.branchCount p.val Z xs : ZMod p.val)
  group : ∀ (cuts : AllCuts h Δ) (j : Fin (2^(h+1))),
    Nat.card (ActualPaths D.program fuel start (RAMMemory.initialMemory (2^r)
      (liveHeader (d := r) hw advice cuts j)) (withinCaps (2^r) (2^e))) =
    specifiedGroupCount fit (fun ξ i μ q => B.denseExponent (fun v => (μ v).val) (ν ξ i μ q))
      E layout init cuts j

attribute [instance] LocalCertificate.pathFintype

variable {B} {n c : ℕ} {hn : 2 ≤ n} {p : Nat.Primes}
  {M : Model p (B.compressorDegree n) (B.compressorEquations hn c)}
  {h Δ a r e w Z radius pc regs pubs : ℕ} {program E : UniversalMachine.Program}
  {hf : ProcessorInput.Fits program n r (2^e) w} {D : Machine w pc regs pubs}
  {fuel : ℕ} {start : BurstRAM.Word w}

/-- The physical single-site equality and the certificate's single-group equality yield the
integer two-mode count. Reducing that count in the finite algebra gives the contradiction. -/
theorem LocalCertificate.false_of_processor
    (C : B.LocalCertificate hn M h Δ a r e w Z radius program hf E D fuel start)
    (processor : ∀ (v : Fin (2^r)) (hdr : ProcessorInput.Header) (sends : RAMLayout.SendArrays r (2^e) w),
      acceptingCount (ProcessorInput.encode program n v hdr (RAMLayout.incidentBits sends v) hf) =
        Nat.card (D.IncidentPaths fuel start (ProcessorInput.headerWord C.hw hdr) ((by decide : 2 ≤ 4).trans C.hw) C.hc v
          (RAMLayout.incidentBits sends v))) : False := by
  let inc := fun ξ i μ (q : C.Path ξ i μ) => B.denseExponent (fun v => (μ v).val) (C.ν ξ i μ q)
  have bound (ξ : Exterior h Δ) (μ : Fin (2^h) → PairNomination n c r)
      (q : (i : Fin (2^h)) → C.Path ξ i (μ i)) (i : Fin (2^h)) (j : Fin (B.denseCount n c)) :
      partialSum (fun v => inc ξ v (μ v) (q v)) i.succ j < 2^Z :=
    prefix_lt C.hZ _ (fun v b => B.denseExponent_lt (μ v) (C.ν ξ v (μ v) (q v))
      (C.hν ξ v (μ v) (q v)) b) i j
  have live := physical_two_modes_realized C.fit inc E C.layout C.init program hf C.advice D fuel start
    C.hw C.hc processor C.group bound (fun xs => C.initial (B.formalExponents xs)) C.hi
    (fun xs => C.histories (B.formalExponents xs))
  apply B.pairedEvaluatorContradiction hn M program hf C.advice C.hR C.hZ C.ν C.hν C.hpair E C.initial C.htail
  simpa only [inc, formalExponents_sum] using live

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
