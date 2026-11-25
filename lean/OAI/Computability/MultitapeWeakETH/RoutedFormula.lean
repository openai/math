import OAI.Computability.MultitapeWeakETH.IncidenceRouting

/-! # Exact counting after one simultaneous permutation of the incidence bits -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT NearSquareRoot.Benes VPVNP Finset
open scoped Classical
noncomputable section

variable {n : ℕ} (F : SAT.CNF (Fin n))

/-- Source addresses supply the free bits. All unused positions, including
destination addresses, have a prescribed initial zero. -/
def Padded {A : Type} (source : Wire F ↪ A) (x : A → Bool) :=
  ∀ i, i ∉ Set.range source → x i = false

def paddedWords {A : Type} (source : Wire F ↪ A) :
    (Wire F → Bool) ≃ {x // Padded F source x} where
  toFun w := ⟨Function.extend source w (fun _ => false),fun i hi => Function.extend_apply' _ _ _ hi⟩
  invFun x e := x.val (source e)
  left_inv w := funext (source.injective.extend_apply w (fun _ => false))
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ Set.range source
    · obtain ⟨e,rfl⟩ := hi
      exact source.injective.extend_apply (fun e => x.val (source e)) (fun _ => false) e
    · exact (Function.extend_apply' (fun e => x.val (source e)) (fun _ => false) i hi).trans (x.property i hi).symm

/-- A table at a site reads the original bits of its source ports and the
permuted bits of its destination ports. Other reads have no effect. -/
def routedHalf {A : Type} (addr : End F ↪ A) (x y : A → Bool) (v : Site F) : (network F).Half v :=
  (fun e _ => x (addr (.inl e)),fun e _ => y (addr (.inr e)))

/-- Count from the two layers of site data, where the second layer is
obtained by routing the first according to the compiler's address permutation. -/
theorem routed_count {A R : Type} [Fintype A] [CommSemiring R] (addr : End F ↪ A)
    (p : Equiv.Perm A) (correct : ∀ e, p (addr (.inl e)) = addr (.inr e)) :
    let source := Function.Embedding.inl.trans addr
    (∑ x : A → Bool, if Padded F source x then
      ∏ v, tables F R v (routedHalf F addr x (x ∘ p.symm) v) else 0) = (SAT.count F:R) := by
  intro source
  let value (x : A → Bool) := ∏ v, tables F R v (routedHalf F addr x (x ∘ p.symm) v)
  change (∑ x, if Padded F source x then value x else 0) = _
  rw [← sum_filter, sum_subtype (p := Padded F source) _ (by simp) value]
  rw [← contract_count F R, NetworkKernel.contract_edgeSum (network F) (tables F R)]
  symm
  apply Fintype.sum_equiv (paddedWords F source)
  intro w
  let x := (paddedWords F source w).val
  have src (e) : x (addr (.inl e)) = w e := source.injective.extend_apply w (fun _ => false) e
  have dst (e) : x (p.symm (addr (.inr e))) = w e := by rw [← correct e,p.symm_apply_apply,src]
  apply prod_congr rfl
  intro v _
  apply congrArg (tables F R v)
  exact Prod.ext (funext fun e => funext fun _ => (src e).symm)
    (funext fun e => funext fun _ => (dst e).symm)

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
