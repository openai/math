import OAI.Computability.VPVNP.CompressedRAMDegree
import OAI.Computability.VPVNP.CursorBranchBudget
import OAI.Computability.VPVNP.RAMApplications

/-!
# The exponent-field bound for the virtual RAM

For all sufficiently large input lengths, every witness of the compressed
virtual path count has total parameter degree below the capacity of a
two-address-width word. The threshold precedes the choice of ring, parameter
assignment, virtual program, fuel, header, and path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Compression CursorRouting NetworkKernel BurstRAM BurstRAM.PrivateRAM CursorBounds Filter

variable {k : Type*} [Field k] {S : BlockSchedule k}

section Count

variable (B : S.Templates) (u : PairExponents B.growthConstant) {b n : ℕ}
variable (hD : 1 < virtualBits b n)
variable (cap : ProcessorBudget n (virtualBits b n) (roundedUp 1 4 n) (wordBits b n))
variable {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
variable (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
variable {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
variable {p r k' : ℕ} (M : Machine (wordBits b n) p r k') (fuel : ℕ)
variable (initial : Word (wordBits b n)) (header : ℕ → Word (wordBits b n))

/-- Equation (12.2) at the virtual site count and quarter-power bucket,
with a specified virtual private fuel. -/
noncomputable def pairRAMCountWithFuel :
    MonomialWitness f (Nat.card (ActualPaths M.program fuel initial
      (RAMMemory.initialMemory (2 ^ virtualBits b n) header)
      (withinCaps (2 ^ virtualBits b n) (2 ^ roundedUp 1 4 n))) : A) := by
  letI : NeZero (virtualBits b n) := ⟨by omega⟩
  exact compressedRAMCount B f hf M fuel initial header cap.tags cap.capFits labels hD _ hT

/-- Equation (12.2) at the paper's virtual private fuel. -/
noncomputable abbrev pairRAMCount :=
  pairRAMCountWithFuel B u hD cap labels hT f hf M (n^10) initial header

end Count

/-- One eventual threshold gives the virtual address and bucket capacities
and the strict exponent bound for every branch, simultaneously over all fuel choices. -/
theorem eventually_pairRAMCountWithFuel_degree (B : S.Templates)
    (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
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
        ∀ c : W.Choice, (∑ l, W.exponents c l) < 2 ^ (2 * addressBits b n) := by
  have hb' : 1 ≤ b := (by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)
  filter_upwards [eventually_pairBranchBounds B u b hb,
    eventually_bothProcessorBudgets hb' (show (0 : ℝ) ≤ 0 from le_rfl) zero_le_one] with n h caps
  obtain ⟨hD, hl, h⟩ := h
  refine ⟨hD, caps.2, hl, ?_⟩
  intro base lanes labels hT A _ f hf p r k' M fuel initial header W c
  let inst : NeZero (virtualBits b n) := ⟨by omega⟩
  obtain ⟨z, hz⟩ := compressedRAMCount_degree B f hf M fuel initial header
    caps.2.tags caps.2.capFits labels hD _ hT c
  have hbranch := h labels hD hT A f hf
  have hbucket : virtualBucket n = 2 ^ roundedUp 1 4 n := by
    simp only [virtualBucket, roundedUp_eq, Nat.cast_one, Nat.cast_ofNat]
  unfold pairInput at hbranch
  rw [hbucket] at hbranch
  exact hz.trans_lt (hbranch z).2.2.2.2.2.2.2

/-- One eventual threshold gives the virtual address and bucket capacities
and the strict exponent bound for every branch, at fuel (n^{10}). -/
theorem eventually_pairRAMCount_degree (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ hD : 1 < virtualBits b n,
      ∃ cap : ProcessorBudget n (virtualBits b n) (roundedUp 1 4 n) (wordBits b n),
      blockCount (u.θ : ℝ) n * S.laneBits ≤ virtualBits b n ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
        {p r k' : ℕ} (M : Machine (wordBits b n) p r k') (initial : Word (wordBits b n))
        (header : ℕ → Word (wordBits b n)),
        let W := pairRAMCount B u hD cap labels hT f hf M initial header
        ∀ c : W.Choice, (∑ l, W.exponents c l) < 2 ^ (2 * addressBits b n) := by
  filter_upwards [eventually_pairRAMCountWithFuel_degree B u b hb] with n h
  obtain ⟨hD, cap, hl, h⟩ := h
  refine ⟨hD, cap, hl, ?_⟩
  intro base lanes labels hT A _ f hf p r k' M initial header
  exact h labels hT A f hf M (n^10) initial header

end CursorNetwork

end VPVNP
end Computability
end OAI
