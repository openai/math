import OAI.Computability.VPVNP.PairRAMDegreeBudget
import OAI.Computability.VPVNP.PairSimulationAssembly
import OAI.Computability.VPVNP.PairSimulationCounters

/-!
# Reading the complete compressed pair's exponent array

The final vertex histograms use the descriptor order of the actual repeated
compressor. Adding them to the shared suffix gives the monomial exponents
in its template alphabet. The prefix holds the nominated production counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Compression CursorRouting NetworkKernel BurstRAM BurstRAM.PrivateRAM CursorBounds Filter
open PairSimulation PairSimulation.LocalHistory

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable (u : PairExponents B.growthConstant) {b n : ℕ} (hD : 1 < virtualBits b n)
variable (cap : ProcessorBudget n (virtualBits b n) (roundedUp 1 4 n) (wordBits b n))
variable {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
variable (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
variable {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
variable {p r k' : ℕ} (M : Machine (wordBits b n) p r k')
variable (fuel : ℕ) (initial : Word (wordBits b n))
variable (header : ℕ → Word (wordBits b n))

/-- Per-vertex template histograms for the chosen virtual fuel, in final-site order. -/
noncomputable def pairRAMHistogramsWithFuel
    (c : (pairRAMCountWithFuel B u hD cap labels hT f hf M fuel initial header).Choice) :
    List (B.Entry → ℕ) := by
  letI : NeZero (virtualBits b n) := ⟨by omega⟩
  let pad := Nat.add_sub_of_le S.degree_bounds.1
  let X := cursorState labels hD pad (ramFieldBits (2 ^ roundedUp 1 4 n) (wordBits b n) :
    RAMSystem (virtualBits b n) → ℕ)
  let P := cursorSiteParsers M fuel initial header cap.tags cap.capFits labels hD pad f
  exact Counters.vertexHistograms _ _ (executeReaders B f hf _ hT X) P.factors P.witnesses c

/-- Per-vertex template histograms, ordered by the actual final-site descriptors. -/
noncomputable abbrev pairRAMHistograms
    (c : (pairRAMCount B u hD cap labels hT f hf M initial header).Choice) :
    List (B.Entry → ℕ) :=
  pairRAMHistogramsWithFuel B u hD cap labels hT f hf M (n^10) initial header c

private theorem twoAddressBits_le_wordBits (b n : ℕ) : 2 * addressBits b n ≤ wordBits b n := by
  change 2 * addressBits b n ≤ (addressBits b n + 10)^4
  calc
    _ ≤ (addressBits b n + 10)^2 := by nlinarith [Nat.zero_le (addressBits b n * addressBits b n)]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

/-- At arbitrary fuel, the ordered visits recover both parts of the live exponent array. -/
theorem pairRAMHistogramsWithFuel_readback
    (c : (pairRAMCountWithFuel B u hD cap labels hT f hf M fuel initial header).Choice)
    (degree : (∑ l, (pairRAMCountWithFuel B u hD cap labels hT f hf M fuel initial header).exponents
      c l) < 2 ^ (2 * addressBits b n))
    {g grammar : ℕ} (order : Fin g ≃ B.Entry) (addr : Word (wordBits b n))
    (fit : addr.val + grammar ≤ 2 ^ wordBits b n) (μ : Fin grammar → Word (2 * addressBits b n))
    (m : Memory (wordBits b n)) (hz : ∀ i : Fin g, m (addr.val + grammar + i) = 0)
    (j : Fin (grammar + g)) :
    let W := pairRAMCountWithFuel B u hD cap labels hT f hf M fuel initial header
    let hist := pairRAMHistogramsWithFuel B u hD cap labels hT f hf M fuel initial header c
    let final := Counters.visit addr.val grammar (fun (h : B.Entry → ℕ) i => h (order i)) hist
      (LiveNominations.stored addr fit μ m)
    (final (addr.val + j)).val =
      Fin.addCases (fun i => (μ i).val) (fun i => W.exponents c (order i)) j := by
  let inst : NeZero (virtualBits b n) := ⟨by omega⟩
  let pad := Nat.add_sub_of_le S.degree_bounds.1
  let X := cursorState labels hD pad (ramFieldBits (2 ^ roundedUp 1 4 n) (wordBits b n) :
    RAMSystem (virtualBits b n) → ℕ)
  let P := cursorSiteParsers M fuel initial header cap.tags cap.capFits labels hD pad f
  apply Counters.live_array_readback _ _ (executeReaders B f hf _ hT X) P.factors P.witnesses
    c order addr fit μ m hz (twoAddressBits_le_wordBits b n) _ j
  rw [← pow_mul, Nat.mul_comm (addressBits b n) 2]
  exact degree

/-- The actual ordered visits recover both parts of the live exponent array. -/
theorem pairRAMHistograms_readback
    (c : (pairRAMCount B u hD cap labels hT f hf M initial header).Choice)
    (degree : (∑ l, (pairRAMCount B u hD cap labels hT f hf M initial header).exponents c l) <
      2 ^ (2 * addressBits b n))
    {g grammar : ℕ} (order : Fin g ≃ B.Entry) (addr : Word (wordBits b n))
    (fit : addr.val + grammar ≤ 2 ^ wordBits b n) (μ : Fin grammar → Word (2 * addressBits b n))
    (m : Memory (wordBits b n)) (hz : ∀ i : Fin g, m (addr.val + grammar + i) = 0)
    (j : Fin (grammar + g)) :
    let W := pairRAMCount B u hD cap labels hT f hf M initial header
    let hist := pairRAMHistograms B u hD cap labels hT f hf M initial header c
    let final := Counters.visit addr.val grammar (fun (h : B.Entry → ℕ) i => h (order i)) hist
      (LiveNominations.stored addr fit μ m)
    (final (addr.val + j)).val =
      Fin.addCases (fun i => (μ i).val) (fun i => W.exponents c (order i)) j :=
  pairRAMHistogramsWithFuel_readback B u hD cap labels hT f hf M (n^10) initial header
    c degree order addr fit μ m hz j

/-- For the paper's virtual dimensions, the final counter array
recovers the two histograms simultaneously for all programs, fuel choices, headers and paths. -/
theorem eventually_pairRAMHistogramsWithFuel_readback (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ hD : 1 < virtualBits b n,
      ∃ cap : ProcessorBudget n (virtualBits b n) (roundedUp 1 4 n) (wordBits b n),
      blockCount (u.θ : ℝ) n * S.laneBits ≤ virtualBits b n ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
        {p r k' : ℕ} (M : Machine (wordBits b n) p r k') (fuel : ℕ)
        (initial : Word (wordBits b n))
        (header : ℕ → Word (wordBits b n)),
        let W := pairRAMCountWithFuel B u hD cap labels hT f hf M fuel initial header
        ∀ (c : W.Choice) {g grammar : ℕ} (order : Fin g ≃ B.Entry) (addr : Word (wordBits b n))
          (fit : addr.val + grammar ≤ 2 ^ wordBits b n)
          (μ : Fin grammar → Word (2 * addressBits b n)) (m : Memory (wordBits b n)),
          (∀ i : Fin g, m (addr.val + grammar + i) = 0) → ∀ j : Fin (grammar + g),
          let hist := pairRAMHistogramsWithFuel B u hD cap labels hT f hf M fuel initial header c
          let final := Counters.visit addr.val grammar (fun (h : B.Entry → ℕ) i => h (order i))
            hist (LiveNominations.stored addr fit μ m)
          (final (addr.val + j)).val =
            Fin.addCases (fun i => (μ i).val) (fun i => W.exponents c (order i)) j := by
  filter_upwards [eventually_pairRAMCountWithFuel_degree B u b hb] with n h
  obtain ⟨hD, cap, hl, h⟩ := h
  refine ⟨hD, cap, hl, ?_⟩
  intro base lanes labels hT A _ f hf p r k' M fuel initial header W c
    g grammar order addr fit μ m hz j
  exact pairRAMHistogramsWithFuel_readback B u hD cap labels hT f hf M fuel initial header c
    (h labels hT A f hf M fuel initial header c) order addr fit μ m hz j

/-- For the paper's virtual dimensions and clock, the final counter array
recovers the two histograms simultaneously for all programs, headers and paths. -/
theorem eventually_pairRAMHistograms_readback (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ hD : 1 < virtualBits b n,
      ∃ cap : ProcessorBudget n (virtualBits b n) (roundedUp 1 4 n) (wordBits b n),
      blockCount (u.θ : ℝ) n * S.laneBits ≤ virtualBits b n ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
        {p r k' : ℕ} (M : Machine (wordBits b n) p r k') (initial : Word (wordBits b n))
        (header : ℕ → Word (wordBits b n)),
        let W := pairRAMCount B u hD cap labels hT f hf M initial header
        ∀ (c : W.Choice) {g grammar : ℕ} (order : Fin g ≃ B.Entry) (addr : Word (wordBits b n))
          (fit : addr.val + grammar ≤ 2 ^ wordBits b n)
          (μ : Fin grammar → Word (2 * addressBits b n)) (m : Memory (wordBits b n)),
          (∀ i : Fin g, m (addr.val + grammar + i) = 0) → ∀ j : Fin (grammar + g),
          let hist := pairRAMHistograms B u hD cap labels hT f hf M initial header c
          let final := Counters.visit addr.val grammar (fun (h : B.Entry → ℕ) i => h (order i))
            hist (LiveNominations.stored addr fit μ m)
          (final (addr.val + j)).val =
            Fin.addCases (fun i => (μ i).val) (fun i => W.exponents c (order i)) j := by
  filter_upwards [eventually_pairRAMHistogramsWithFuel_readback B u b hb] with n h
  obtain ⟨hD, cap, hl, h⟩ := h
  refine ⟨hD, cap, hl, ?_⟩
  intro base lanes labels hT A _ f hf p r k' M initial header
  exact h labels hT A f hf M (n^10) initial header

end CursorNetwork

end VPVNP
end Computability
end OAI
