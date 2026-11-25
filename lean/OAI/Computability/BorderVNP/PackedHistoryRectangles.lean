import OAI.Computability.BorderVNP.PackedHistoryNestedCost
import OAI.Computability.BorderVNP.ShortenPublicPaddedWords

/-! # Charging nested Boolean epochs at their real sparse site and cable rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Crossing Shortening.PublicCapacity Shortening.Adaptive Packing TeamScales Filter VPVNP.VerifierNetwork

variable {D m k b : ℕ} {K : Type*} [Field K] (paid : PaidIdentity K D m)

/-- The measured per-row work of a public node on its actual site/cable rectangle. -/
def rowWork (C V L exp : ℕ) (s : Shape) : ℕ := C * s.volume V * L^exp

/-- The actual gate and count-field bounds on the bottom, both boundaries of every
epoch, and every combined child tuple. They use the specified seed numbers at
each level and include the raw joined children in the inner node's rectangle. -/
structure RectangleWork {T : ℕ} {σ : Type} [Fintype σ] {O : ℕ → Type} {W G : ℕ → ℕ → Type}
    [∀ t, Fintype (O t)] [∀ t j, Fintype (W t j)] [∀ t j, Fintype (G t j)]
    (extra V L C exp : ℕ) (seeds : ℕ → ℕ → ℕ) (init : Shape) (f : Frame σ (O 0))
    (inner : ∀ t, t<T → Steps k b (W t) (G t))
    (pre : ∀ t, t<T → Frame (Fin (k^b) × O t) (Fin (k^b) × W t 0))
    (post : ∀ t, t<T → Frame ((Fin (k^b) × O t) ⊕ W t b) (O (t+1))) : Prop where
  /-- Fixed bottom bundle geometry. -/
  leaf : f.size+1 ≤ rowWork C V L exp init
  /-- Input subdivision reads this epoch's original site pack. -/
  start : ∀ t ht, (pre t ht).size ≤ rowWork C V L exp (epochRows paid k b extra seeds init t)
  /-- The seam motion uses the final sewn directory at this epoch. -/
  finish : ∀ t ht, (post t ht).size ≤ rowWork C V L exp (epochRows paid k b extra seeds init (t+1))
  /-- The actual gate count and literal count-field size of every internal round. -/
  round : ∀ t (ht : t<T) j (hj : j<b),
    let old := epochRows paid k b extra seeds init t
    let sub := (combineRows paid k (seeds t) (old.subdivide extra) j).parallel k
    (inner t ht j hj).size + (2*k+4) ≤ rowWork C V L exp sub ∧ Fintype.card (G t j) ≤ rowWork C V L exp sub

set_option maxHeartbeats 900000 in
/-- The entire realized rectangular epoch traversal, including its actual guess bank,
fits below exponent 0.92. The only size assumptions refer to individual public frames
and fields on the actual rectangles. The factor for reserved seeds and bands follows
from the concrete allocation recurrence. -/
theorem eventually_rectangular_history_92 {α τ : ℝ} (extra bins C exp Q : ℕ)
    (hα : α < 1/1000) (hτ : 0<τ) (hτ' : τ<α/100) (hk : 0<k)
    (hteams : τ*Real.logb 2 (k^b : ℕ) ≤ α)
    (growth : τ*Real.logb 2 (Shortening.PublicCapacity.epochFactor paid k b extra bins) ≤ α/10) :
    ∃ ω : ℝ, 0<ω ∧ ∀ A : ℝ, 0≤A → ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ) ≤ 2^((n:ℝ)^ω) →
      let T := epochs τ n
      ∀ (V : ℕ) (seeds : ℕ → ℕ → ℕ) (init : Shape),
        (∀ t j, seeds t j ≤ V*bins) → (init.volume V:ℝ) ≤ A*(r*(n:ℝ)^(9/10:ℝ)) →
      ∀ (σ : Type) [Fintype σ] (O : ℕ → Type) (W G : ℕ → ℕ → Type)
        [∀ t, Fintype (O t)] [∀ t j, Fintype (W t j)] [∀ t j, Fintype (G t j)]
        (f : Frame σ (O 0)) (inner : ∀ t, t<T → Steps k b (W t) (G t))
        (pre : ∀ t, t<T → Frame (Fin (k^b) × O t) (Fin (k^b) × W t 0))
        (post : ∀ t, t<T → Frame ((Fin (k^b) × O t) ⊕ W t b) (O (t+1))),
        RectangleWork paid extra V (logWidth r n) C exp seeds init f inner pre post →
        ((Q*(compile (nestedSteps inner pre post) T le_rfl (repeatLeaf (k^b) f T)).size +
          Fintype.card (Slot (k^b) (fun t => Slot k (G t) b) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ) := by
  let g := Shortening.PublicCapacity.epochFactor paid k b extra bins
  have hg : 1≤g := epochFactor_pos paid hk b extra bins
  obtain ⟨ω,hω,work⟩ := eventually_nested_history_92 b exp Q hα hτ hτ' hk hteams
    (by exact_mod_cast hg : 1≤(g:ℝ)) growth
  refine ⟨ω,hω,fun A hA => ?_⟩
  filter_upwards [work (C*A) (by positivity), eventually_ge_atTop 1] with n hwork hn
  intro r hr hr' T V seeds init hseeds hinit σ _ O W G _ _ _ f inner pre post measured
  let L := logWidth r n
  let vol := g^T * init.volume V
  let M := C*vol*L^exp
  have hboundary (t : ℕ) (ht : t≤T) : (epochRows paid k b extra seeds init t).volume V ≤ vol :=
    (epochRows_le paid hk b extra V bins seeds hseeds init t).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hg ht))
  have hrow {s : Shape} (cap : s.volume V ≤ vol) : rowWork C V L exp s ≤ M :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cap)
  have hw : (1:ℝ) ≤ width n α := by
    have hα0 : 0≤α := by linarith
    have hnat : 1 ≤ width n α := Nat.le_floor (by simpa using Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ)) hα0)
    exact_mod_cast hnat
  have cap : (M:ℝ) ≤ C*A*(r*(n:ℝ)^(9/10:ℝ))*((g:ℝ)^T*width n α)*(logWidth r n:ℝ)^exp := by
    dsimp [M,vol,L]
    push_cast
    calc
      _ ≤ (C:ℝ)*((g:ℝ)^T*(A*(r*(n:ℝ)^(9/10:ℝ))))*(logWidth r n:ℝ)^exp := by gcongr
      _ ≤ (C:ℝ)*((g:ℝ)^T*(A*(r*(n:ℝ)^(9/10:ℝ))))*(width n α:ℝ)*(logWidth r n:ℝ)^exp := by
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hw) (by positivity)
      _ = _ := by ring
  apply hwork r hr hr' M cap σ O W G f inner pre post
  · exact measured.leaf.trans (hrow (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega : 0<g))))
  · intro t ht
    exact ⟨(measured.start t ht).trans (hrow (hboundary t ht.le)),
      (measured.finish t ht).trans (hrow (hboundary (t+1) ht))⟩
  · intro t ht j hj
    exact (measured.round t ht j hj).1.trans (hrow (joinedRows_le paid hk b extra V bins seeds hseeds init ht hj))
  · intro t ht j hj
    exact (measured.round t ht j hj).2.trans (hrow (joinedRows_le paid hk b extra V bins seeds hseeds init ht hj))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
