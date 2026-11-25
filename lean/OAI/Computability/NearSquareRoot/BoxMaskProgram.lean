import OAI.Computability.NearSquareRoot.BoxMaskHeader
import OAI.Computability.NearSquareRoot.BoxMask
import OAI.Computability.NearSquareRoot.InterchangeSignMachine
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth

/-! # Fixed-tape linear-time generation of the entire validity mask

Starting from the unary address width, perform the polynomial gcd search for the
CRT directory and expand it into the physical array's Boolean mask. The finite
exception in the Jacobsthal proof concerns the assurance of a valid directory;
its nonconstructive threshold is absent from the command the compiler runs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxMaskProgram

open IntegerMultiplication Code BoxScale CoprimeBox

/-- Polynomial setup in the address width is linear in the number of array cells,
with one coefficient for all `k` (including small address widths). -/
theorem tally_setup {A : Type} [Codec A] (f : Tally → A) (hf : Poly f) :
    Task (fun k : ℕ => 2 ^ k) (fun k => send (tally k)) (fun k => send (f (tally k))) := by
  have hw : Dom (fun k : ℕ => k) (fun k => size (tally k)) := by
    exact ⟨1, 2, fun k => by simp [size_tally]⟩
  obtain ⟨b, ⟨d, C, hb⟩, hprog⟩ := hf.on hw
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (eventually_polynomial_le_array_length (C : ℝ) (by positivity) d)
  apply hprog.bound (C * (K+1)^d + 1)
  intro k
  have hpool := hb k
  by_cases hk : K ≤ k
  · have hlarge : C * (1+k)^d ≤ (2:ℕ)^k := by exact_mod_cast hK k hk
    rw [Nat.add_comm 1 k] at hlarge
    calc
      _ ≤ 2^k+1 := Nat.succ_le_succ (hpool.trans hlarge)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  · have hsmall : C * (k+1)^d ≤ C * (K+1)^d := by gcongr; omega
    exact (Nat.succ_le_succ (hpool.trans hsmall)).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- The Boolean array in the same order as the physical records. -/
def mask (k : ℕ) : List Bool := BoxOrder.expand (BoxOrder.shape (box k))

/-- The conditional input domain permits direct attachment of a small-input fallback. -/
theorem task {X : Type} (k : X → ℕ) (valid : ∀ x, BoxShape.Valid (k x) (width (k x)) (box (k x))) :
    Task (fun x => 2 ^ k x) (fun x => send (tally (k x))) (fun x => send (mask (k x))) := by
  have setup := (tally_setup BoxMaskHeader.encoded BoxMaskHeader.encoded_poly).on k
  have s : ∀ x, BoxMaskHeader.encoded (tally (k x)) = BoxMask.header (BoxOrder.shape (box (k x))) := by
    intro x; simp only [BoxMaskHeader.encoded, tally_length]; rfl
  simp only [s] at setup
  exact (setup.compose (BoxMask.of_valid k (width ∘ k) (box ∘ k) valid)).bound 2
    (by intro x; omega)

theorem carries {X : Type} (k : X → ℕ) (valid : ∀ x, BoxShape.Valid (k x) (width (k x)) (box (k x))) :
    Carries (fun x => ((2 ^ k x : ℕ) : ℝ)) (fun x => send (tally (k x)))
      (fun x => send (mask (k x))) := by
  have hpos (x : X) : 1 ≤ ((2 ^ k x : ℕ) : ℝ) := by exact_mod_cast (Nat.one_le_pow _ _ (by decide : 0 < 2))
  refine ⟨⟨hpos, _, task k valid, 2, fun x => ?_⟩, 2, fun x => ?_⟩
  · have := hpos x
    dsimp only
    push_cast at *
    linarith
  · change ((size (tally (k x)) : ℕ) : ℝ) ≤ 2 * ((2 ^ k x : ℕ) : ℝ)
    exact_mod_cast (show size (tally (k x)) ≤ 2 * 2 ^ k x from by
      simp only [size_tally, tally_length]; have := (k x).lt_two_pow_self; omega)

/-- A single concrete finite-tape machine generates exactly the validity stream in
`O(2^k)` time and visited cells for every sufficiently large `k`. -/
theorem machine : ∃ K : ℕ, LinearTreeMachine (fun k : {j : ℕ // K ≤ j} => 2 ^ k.val)
    (fun k => send (tally k.val)) (fun k => send (mask k.val)) := by
  obtain ⟨K, hK⟩ := eventually_valid
  exact ⟨K, linearTreeMachine_of_carries (carries Subtype.val fun x => hK x.val x.property)⟩

end BoxMaskProgram

end NearSquareRoot
end Computability
end OAI
