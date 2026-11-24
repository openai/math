import OAI.Computability.VPVNP.FixedProgramModelData
import OAI.Computability.VPVNP.PaperPairParameters
import OAI.Computability.VPVNP.PairRAMDegreeBudget
import OAI.Computability.VPVNP.PrimedCounterTranscriptCountParameters

/-!
# The concrete auxiliary pair data of the fixed diagonal program

At each admissible length choose one uniform coefficient-counter layout
for each pair index. All exterior bit strings and nominations use that same
layout. Their compressed witnesses use the actual virtual machine, its
actual reset word, private clock, and header. Thus the exponent histogram
returned by the pair path and its algebraic weight belong to the same
finite occurrence. The lane numbering reverses the coordinates within
each address block, as in the physical cursor descriptor reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM BurstRAM.PrivateRAM LiveProgram CursorBounds CursorNetwork Compression
open PrimedInputRAM PrimedStackRAM CutSchedule ExponentTrace Filter
open scoped Classical

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} (D : FixedProgramDiagonal.Program)
    (B : S.Templates) (u : PairExponents B.growthConstant) {n C : ℕ} (hn : 2 ≤ n)

/-- Zero-based indices of the pairs at the fixed program's chain height, with one index for
each first-half group. -/
abbrev groupIndices (n : ℕ) := Fin (2^(D.chainHeight n))

/-- Primed input lengths for one pair, including the two exterior cuts and the intervening cut,
using the fixed program's chain height, cut width and advice length. -/
abbrev pairLengths (i : D.groupIndices n) :=
  PairedChain.lengths (D.chainHeight n) (n^D.constants.deltaPower) (n^D.constants.advicePower) i

/-- Type of primed RAM input layouts for this pair's field lengths and the program's physical
site exponent, bucket size and word width. -/
abbrev pairLayout (i : D.groupIndices n) :=
  PrimedInputRAM.Layout (D.pairLengths i) n (D.geometry n).d (D.geometry n).H (D.geometry n).w

/-- Production histograms nominated at length n and circuit exponent C. Each production count
is strictly less than `2^(2*d)`, where d is the physical site address width. -/
abbrev pairNom (n C : ℕ) := BlockSchedule.Templates.PairNomination n C (D.geometry n).d

/-- Degree, root and production histogram passed to the actual auxiliary program. -/
noncomputable def auxData {i : D.groupIndices n} (Q : D.pairLayout i)
    (hdr : Header (D.pairLengths i) → Bool) (μ : D.pairNom n C) :
    PrimedCounter.Data Q (n^(C+5)) :=
  PrimedCounter.Data.ofNomination Q ⟨n-1,by omega⟩ ⟨0,pow_pos (by omega) _⟩ hdr μ

/-- Resource conditions on the virtual processor at length n, using the virtual site exponent,
the rounded quarter-power bucket exponent and the fixed program's RAM word width. -/
abbrev virtualCap (n : ℕ) := ProcessorBudget n (virtualBits D.addressFactor n)
  (roundedUp 1 4 n) (CursorBounds.wordBits D.addressFactor n)

/-- Number of lane coordinates used by all scheduled compression blocks, equal to the block
count times the lanes per block. -/
noncomputable def reservedLanes (n : ℕ) := blockCount (u.θ : ℝ) n * S.laneBits

/-- Physical choices shared by all calls to the auxiliary pair program
at this one length. The degree inequality precedes the choice of
specialization, input, and path. -/
structure VirtualPairs (C : ℕ) where
  /-- Primed input layout for each pair index at this length, shared across all advice,
  exterior bits and nominations for that index. -/
  layout : (i : D.groupIndices n) → D.pairLayout i
  literal : ∀ i, (layout i).program = D.literal
  scratch : ∀ i, (layout i).scratchBase = 2^(virtualBits D.addressFactor n)
  cap : D.virtualCap n
  counts : ∀ i hdr (μ : D.pairNom n C), PrimedCounter.Resources.Counts (D.auxData hn (layout i) hdr μ) μ cap
  dimension : 1 < virtualBits D.addressFactor n
  lanes : reservedLanes B u n ≤ virtualBits D.addressFactor n
  degree : ∀ (A : Type) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
    (i : D.groupIndices n) (hdr : Header (D.pairLengths i) → Bool) (μ : D.pairNom n C),
    let d := D.auxData hn (layout i) hdr μ
    let W := pairRAMCountWithFuel B u dimension cap (laneLabels _ _ lanes) le_rfl
      f hf d.machine d.fuel 0 d.initial
    ∀ q : W.Choice, (∑ l, W.exponents q l) < 2^(2*(D.geometry n).d)

variable {D B u hn}

/-- Instantiate the auxiliary coefficient counter at this pair index with its layout, the
header derived from advice and exterior cuts, and the nominated production counts. -/
noncomputable def VirtualPairs.data (V : D.VirtualPairs B u hn C) (advice : Bits (n^D.constants.advicePower))
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C) :=
  D.auxData hn (V.layout i) (PairedChain.headers advice ξ i) μ

/-- Compressed count witness for the nominated auxiliary machine under the given label
solution, using its actual private fuel, zero starting state and initialized memory. -/
noncomputable def VirtualPairs.witness (V : D.VirtualPairs B u hn C) {A : Type} [CommRing A]
    (f : B.Entry → A) (hf : B.IsSolution f) (advice : Bits (n^D.constants.advicePower))
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C) :=
  let d := V.data advice ξ i μ
  pairRAMCountWithFuel B u V.dimension V.cap (laneLabels _ _ V.lanes) le_rfl
    f hf d.machine d.fuel 0 d.initial

variable {p : Nat.Primes} {M : LabelEvaluator.Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (fit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)

private theorem input_program_congr {n r bucket w : ℕ} {L : PrimedInputRAM.Lengths}
    {p q : UniversalMachine.Program} (hp : ProcessorInput.Fits p n r bucket w)
    (hq : ProcessorInput.Fits q n r bucket w) (eq : p = q) (header : Header L → Bool) :
    PrimedInputRAM.input p hp header = PrimedInputRAM.input q hq header := by
  cases eq
  rfl

/-- The finite paths, their exponents, and their joint coefficient identity
for the literal processor and precisely the same advice used at the midpoint. -/
noncomputable def VirtualPairs.pairData (V : D.VirtualPairs B u hn C) : PairData data fit where
  Path ξ i μ := (V.witness (B.compressorValues hn M) (B.compressorValues_solution hn M) data.advice ξ i μ).Choice
  pathFintype _ _ _ := inferInstance
  ν ξ i μ := (V.witness (B.compressorValues hn M) (B.compressorValues_solution hn M) data.advice ξ i μ).exponents
  bounded ξ i μ q l := by
    have h := V.degree M.algebra (B.compressorValues hn M) (B.compressorValues_solution hn M)
      i (PairedChain.headers data.advice ξ i) μ q
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans_lt h
  weight ξ i μ := by
    let W := V.witness (B.compressorValues hn M) (B.compressorValues_solution hn M) data.advice ξ i μ
    have hw := W.evaluates
    have hc := (V.counts i (PairedChain.headers data.advice ξ i) μ).native
    have eq := input_program_congr (V.layout i).fits fit (V.literal i) (PairedChain.headers data.advice ξ i)
    rw [show (D.auxData hn (V.layout i) (PairedChain.headers data.advice ξ i) μ).header =
      PairedChain.headers data.advice ξ i from rfl, eq] at hc
    exact hw.trans (congrArg (fun x : ℕ => (x : M.algebra)) hc)

/-- A fixed exponent covering all grammar labels before the address exponent
is selected. It depends only on the hypothesized circuit exponent. -/
def grammarCapacityPower (C : ℕ) := 3 + 3*(C+5)

theorem grammar_count_le (n C : ℕ) (hn : 2 ≤ n) :
    labelCount n n (n^(C+5)) ≤ n^grammarCapacityPower C := by
  let H := n^(C+5)
  have hH : 0 < H := Nat.pow_pos (by omega)
  have hH' : H ≤ H^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hH (by decide : 1 ≤ 3)
  have hch : n.choose 2 ≤ n*n := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  change H*n*2+n.choose 2*H*H*H ≤ _
  have h1 : H*n*2 ≤ n*n*H^3 := calc
    _ ≤ H*n*n := Nat.mul_le_mul_left _ hn
    _ = n*n*H := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hH'
  have h2 : n.choose 2*H*H*H ≤ n*n*H^3 := calc
    _ = n.choose 2*H^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hch
  calc
    _ ≤ 2*(n*n*H^3) := by omega
    _ ≤ n*(n*n*H^3) := Nat.mul_le_mul_right _ hn
    _ = n^grammarCapacityPower C := by
      unfold grammarCapacityPower H
      rw [pow_add n 3 (3*(C+5)), Nat.mul_comm 3 (C+5), pow_mul n (C+5) 3]
      ring

variable (D B u)

/-- At sufficiently large lengths the auxiliary virtual layouts and their
path identities exist simultaneously at every pair, before the advice,
exterior cuts and nominations are selected. -/
theorem eventually_virtualPairs (C : ℕ)
    (hnumerator : D.numerator = (liveRatio u).num) (hdenominator : D.denominator = (liveRatio u).den)
    (hb : max S.laneBits 5 ≤ D.addressFactor)
    (hB : max (max (D.constants.chainPower+1) (D.constants.chainPower+D.constants.deltaPower))
      (max D.constants.advicePower (grammarCapacityPower C)) + 2 ≤ D.addressFactor) :
    ∀ᶠ n : ℕ in atTop, ∀ hn : 2 ≤ n, Nonempty (D.VirtualPairs B u hn C) := by
  have hd : 0 < (u.δ : ℝ) := by exact_mod_cast u.delta_pos
  have hd' : (u.δ : ℝ) ≤ 1 := by exact_mod_cast (show u.δ ≤ 1 by linarith [u.theta_lt,u.delta_lt])
  filter_upwards [PrimedCounter.Resources.eventually_counts D.literal D.constants.chainPower
    D.constants.advicePower D.constants.deltaPower (grammarCapacityPower C) D.addressFactor hB hd hd',
    eventually_pairRAMCountWithFuel_degree.{v,0} B u D.addressFactor hb] with n counts degree hn
  obtain ⟨hD,cap,hLane,hdeg⟩ := degree
  have hbuck : liveBucket (u.δ : ℝ) n = (D.geometry n).H := by
    change liveBucket (u.δ : ℝ) n = 2^(roundedUp D.numerator D.denominator n)
    rw [hnumerator,hdenominator,← liveCapacity_eq u n]
    rfl
  have localLayouts (i : D.groupIndices n) :
      ∃ Q : D.pairLayout i, Q.program = D.literal ∧ Q.scratchBase = 2^(virtualBits D.addressFactor n) ∧
        ∀ hdr (μ : D.pairNom n C), PrimedCounter.Resources.Counts (D.auxData hn Q hdr μ) μ cap := by
    have hh := counts i (n^(C+5)) (grammar_count_le n C hn)
    dsimp only at hh
    rw [hbuck] at hh
    obtain ⟨Q,hp,hbase,cap',hc⟩ := hh
    exact ⟨Q,hp,hbase,fun hdr μ => hc _ _ hdr μ (by change n-1+1=n; omega)⟩
  choose Q hq hs hc using localLayouts
  refine ⟨⟨Q,hq,hs,cap,hc,hD,hLane,?_⟩⟩
  intro A inst f hf i hdr μ d W q
  exact hdeg (laneLabels _ _ hLane) le_rfl A f hf d.machine d.fuel 0 d.initial q

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
