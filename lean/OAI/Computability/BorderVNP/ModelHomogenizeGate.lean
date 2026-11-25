import OAI.Computability.BorderVNP.ModelGateExtension
import OAI.Computability.VPVNP.GradedComponents

/-! # Homogenization of a multiplication gate

For degree `k` there are `k + 1` possible degree splits. Reading already computed
components through their gate references, one multiplication and one addition per
split suffice to accumulate the product component in any characteristic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Homogenize

open VPVNP MvPolynomial

variable {R σ : Type*} [CommRing R] {n : ℕ}

/-- Accumulating a sum of products costs two gates per term and retains the input wires. -/
theorem append_sum_products {ι : Type*} (p : Program R σ n) (s : Finset ι)
    (a b : ι → MvPolynomial σ R) (ha : ∀ i ∈ s, HasWire p (a i))
    (hb : ∀ i ∈ s, HasWire p (b i)) :
    ∃ l ≤ n + 2 * s.card, ∃ q : Program R σ l, Preserves p q ∧
      HasWire q (∑ i ∈ s, a i * b i) :=
  Interpreted.append_sum_products C X p s (by simpa only [map_zero] using Interpreted.hasWire_const C X p 0) a b ha hb

/-- One degree component of a product costs at most two gates per degree split.
Every existing reference survives the extension, including the components of both inputs. -/
theorem append_product_component (p : Program R σ n) (k : ℕ) {a b : MvPolynomial σ R}
    (ha : ∀ i ≤ k, HasWire p (homogeneousComponent i a))
    (hb : ∀ i ≤ k, HasWire p (homogeneousComponent i b)) :
    ∃ l ≤ n + 2 * (k + 1), ∃ q : Program R σ l, Preserves p q ∧
      HasWire q (homogeneousComponent k (a * b)) := by
  rw [homogeneousComponent_mul]
  simpa only [Finset.Nat.card_antidiagonal] using
    append_sum_products p (Finset.antidiagonal k) (fun ij => homogeneousComponent ij.1 a)
      (fun ij => homogeneousComponent ij.2 b)
      (fun ij hij => ha ij.1 ((Finset.mem_antidiagonal.mp hij) ▸ Nat.le_add_right ..))
      (fun ij hij => hb ij.2 ((Finset.mem_antidiagonal.mp hij) ▸ Nat.le_add_left ..))

end Homogenize

end BorderVNP
end Computability
end OAI
