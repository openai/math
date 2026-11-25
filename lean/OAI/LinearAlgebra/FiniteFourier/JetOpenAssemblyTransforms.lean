import OAI.LinearAlgebra.FiniteFourier.JetOpenAssembly
import OAI.LinearAlgebra.FiniteFourier.JetAssembly.JetOpenAssemblyCost
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyPacking
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyGather
import OAI.LinearAlgebra.FiniteFourier.ProtectedCircuit
import OAI.LinearAlgebra.FiniteFourier.IntegralOpenDescent

/-! # From the multiplication transforms to a protected open list

The transforms start and end in the quadratic coordinates of the three power
bases. Input packing, the split products, and output gathering then give a single
localized open list. The estimates retain the child lengths and all linear costs.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped BigOperators

variable {R S A U B : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra S A]
variable {e h : B → ℕ} {a d : ℕ}

/-- The two coordinate transforms for multiplication in the packed algebra.
This identity applies to any representatives of the inputs and block products. -/
def RecoversAlgebraProduct (φ : R →+* S) (η : S) (m : B → S[X])
    (basis : Module.Basis U S A)
    (forward : Circuit R (U × Fin 2) (JetBlockInput e h) a)
    (backward : Circuit R (JetBlockOutput e h) (U × Fin 2) d) : Prop :=
  ∀ (v w : A) (x y : U × Fin 2 → R),
    (∀ i, QuadraticDescent.decode φ η x i = basis.repr v i) →
    (∀ i, QuadraticDescent.decode φ η y i = basis.repr w i) →
    ∀ z : JetBlockOutput e h → R,
    (∀ b, jetOutputValueOver φ η (m b) (fun t => z ⟨b,t⟩) =
      jetBlockValue φ η m (forward.eval x) b * jetBlockValue φ η m (forward.eval y) b) →
    ∀ i, QuadraticDescent.decode φ η (backward.eval z) i = basis.repr (v*w) i

/-- Certify the two transforms independently against their algebraic maps.
Only products of two transformed inputs need a left inverse. -/
theorem RecoversAlgebraProduct.of_blocks (φ : R →+* S) (η : S) (m : B → S[X])
    (basis : Module.Basis U S A)
    (forward : Circuit R (U × Fin 2) (JetBlockInput e h) a)
    (backward : Circuit R (JetBlockOutput e h) (U × Fin 2) d)
    (toBlocks : A → ∀ b, JetQuotient (m b) (h b))
    (fromBlocks : (∀ b, JetQuotient (m b) (h b)) → A)
    (hin : ∀ v x, (∀ i, QuadraticDescent.decode φ η x i = basis.repr v i) →
      ∀ b, jetBlockValue φ η m (forward.eval x) b = toBlocks v b)
    (hout : ∀ z i, QuadraticDescent.decode φ η (backward.eval z) i =
      basis.repr (fromBlocks (fun b => jetOutputValueOver φ η (m b) (fun t => z ⟨b,t⟩))) i)
    (hprod : ∀ v w, fromBlocks (fun b => toBlocks v b * toBlocks w b) = v * w) :
    RecoversAlgebraProduct φ η m basis forward backward := by
  intro v w x y hx hy z hz i
  rw [hout, ← hprod]
  congr 3
  funext b
  rw [hz b, hin v x hx, hin w y hy]

variable [Fintype B] {n E r N : ℕ}

/-- A product transform on the mixed-radix packing gives a common-encoder open
formula for the ordinary product. The gather costs at most one gate per address. -/
theorem exists_packedOpenConvolution (φ : R →+* S) (η : S)
    (hcoord : Function.Injective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (m : B → S[X]) (jets : ∀ b, JetCircuitsOver φ η (m b) (e b) (h b))
    (basis : Module.Basis (Fin E × Fin r × Fin N) S A) (u v w : A)
    (hb : ∀ i, basis i = u^i.1.val * v^i.2.1.val * w^i.2.2.val)
    (hE : 0 < E) (hr : 0 < r) (hcap : 8*n ≤ E*r*N)
    (forward : Circuit R ((Fin E × Fin r × Fin N) × Fin 2) (JetBlockInput e h) a)
    (backward : Circuit R (JetBlockOutput e h) ((Fin E × Fin r × Fin N) × Fin 2) d)
    (correct : RecoversAlgebraProduct φ η m basis forward backward) :
    ∃ p : OpenConvolution R n (B × Fin 3) (jetBlockLength e h), p.RealizesMultiple 1 ∧
      p.linearCost ≤ 2*a+d+E*r*N+∑ b, JetAssembly.blockCost (e b) (h b) := by
  obtain ⟨g, hg, gather, hgather⟩ := exists_quadraticGather_circuit φ η hcoord
    basis u v w hb hE hr hcap
  let pack := quadraticPackingCircuit (R := R) hE hr hcap
  obtain ⟨l, hl, extract, hextract⟩ := circuit_comp pack forward
  obtain ⟨t, ht, recover, hrecover⟩ := circuit_comp backward gather
  have H : RecoversFromJetProducts φ η m extract recover := by
    intro x y z hz k
    rw [hrecover]
    apply hgather x y (backward.eval z)
    apply correct _ _ (pack.eval x) (pack.eval y)
      (quadraticPackingCircuit_decode φ η basis hE hr hcap x)
      (quadraticPackingCircuit_decode φ η basis hE hr hcap y) z
    simpa only [hextract] using hz
  obtain ⟨p,hp,hcost⟩ := exists_openConvolution_of_jetBlocks φ η m jets extract recover H
  refine ⟨p,hp,?_⟩
  simp only [JetAssembly.blockCost, ← Nat.add_assoc] at hcost ⊢
  omega

/-- The embedding of a protected base ring gives the localized rational circuit
consumed by integral open descent. The map preserves every gate count. -/
theorem OpenConvolution.localized_mapProtected {L : Finset ℕ} {J : Type*} {len : J → ℕ}
    (p : OpenConvolution (protectedRationals L) n J len) (hp : p.RealizesMultiple 1) :
    (p.mapCoeff (protectedRationals L).subtype).Localized (denominatorsAvoiding L) ∧
    (p.mapCoeff (protectedRationals L).subtype).linearCost = p.linearCost := by
  exact ⟨⟨p.input.denominatorsIn_protectedRationals, p.output.denominatorsIn_protectedRationals,
    by simpa only [map_one] using hp.mapCoeff (protectedRationals L).subtype⟩, rfl⟩

end FiniteFourier
end LinearAlgebra
end OAI
