import OAI.Computability.VPVNP.CloudReplacement
import OAI.Computability.VPVNP.PortDenominator
import OAI.Computability.VPVNP.PortMatching

/-!
# Realizing a lazy Cesàro walk by a matching

Section 5.3 of *VP and VNP differ over every field* takes one matching step
at a uniform port to implement the averaged old walk exactly. Combining
integer walk counts with port reversal gives the transition matrix itself.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One involution implements the mixture of the first `t` positive powers
of the lazy walk of a symmetric regular graph. Self-transitions use fixed ports. -/
theorem exists_cesaroPortMatching (G : Matrix V V ℕ) {b t Q : ℕ}
    (hb : 0 < b) (ht : 0 < t) (hQ : 0 < Q)
    (hs : ∀ v w, G v w = G w v) (hrow : ∀ v, ∑ w, G v w = b)
    (hdiv : t * (2 * b) ^ t ∣ Q) :
    ∃ σ : Equiv.Perm (V × Fin Q), Function.Involutive σ ∧
      portWalk σ = cesaroWalk (lazyWalk (fun v w ↦ (G v w : ℝ) / b)) t ∧
      (∀ p, (σ p).1 = p.1 → σ p = p) := by
  obtain ⟨a, hasym, harow, hcounts⟩ := exists_cesaroPortCounts ℝ G hb ht hs hrow hdiv
  obtain ⟨σ, hinv, hfiber, hfix⟩ := exists_portMatching a hasym harow
  refine ⟨σ, hinv, ?_, hfix⟩
  ext v w
  rw [portWalk, hfiber, Fintype.card_fin]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hQ.ne')).mpr
  rw [mul_comm]
  exact hcounts v w

end SpectralGeometry

end VPVNP
end Computability
end OAI
