import OAI.Computability.MultitapeWeakETH.SwitchChecks

/-! # Contraction of the packed lifted switch state -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open NearSquareRoot.Benes VPVNP VPVNP.Compression VPVNP.NetworkKernel Finset
open scoped Classical
noncomputable section

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)
variable {R : Type} [CommSemiring R]

abbrev Validator (g l : ℕ) (R : Type) := BitWord g → (Fin (2^l) → Bool) → (Fin (2^l) → Bool) → R

def factors (f : Validator g l R) : Factors R (state stages a g l).network :=
  fun (v : site m g) b => if Checks stages t ha v b then
    if v.1 = 0 then f v.2 (emit stages t ha v b) (receive stages t ha v b) else 1
  else 0

def localBank (x : Word (g+l) → Bool) (v : BitWord g) := fun s => x (addressAt v s)

private def rootProduct (f : Validator g l R) (z : Payloads stages a g l) :=
  ∏ v : BitWord g, f v (emit stages t ha (0,v) (shared stages z (0,v)))
    (receive stages t ha (0,v) (shared stages z (0,v)))

private theorem weight (f : Validator g l R) (z : Payloads stages a g l) :
    (∏ v, factors stages t ha f v (shared stages z v)) =
      if Legal stages t ha z then rootProduct stages t ha f z else 0 := by
  by_cases h : Legal stages t ha z
  · rw [ite_eq_left h]
    unfold factors
    change (∏ v : Fin (m+2) × BitWord g, _) = _
    rw [Fintype.prod_prod_type]
    rw [prod_eq_single 0]
    · apply prod_congr rfl
      intro v _
      rw [ite_eq_left (h (0,v))]
      exact ite_eq_left rfl
    · intro i _ hi
      apply prod_eq_one
      intro v _
      rw [ite_eq_left (h (i,v))]
      exact ite_eq_right hi
    · simp
  · rw [ite_eq_right h]
    obtain ⟨v,hv⟩ := not_forall.mp h
    exact prod_eq_zero (mem_univ v) (ite_eq_right hv)

/-- The full tensor contraction is one product of validators per input
bank. Each receives the final bank pulled through the complete permutation. -/
theorem contract_state (f : Validator g l R) :
    contract (state stages a g l).network (factors stages t ha f) =
      ∑ x : Word (g+l) → Bool, ∏ v, f v (localBank x v)
        (localBank (x ∘ (SwitchFlow.finish (switchAt stages t)).symm) v) := by
  rw [contract_edgeSum]
  change (∑ z : Payloads stages a g l, ∏ v, factors stages t ha f v (shared stages z v)) = _
  simp_rw [weight]
  rw [← sum_filter, sum_subtype (p := Legal stages t ha) _ (by simp) (rootProduct stages t ha f)]
  symm
  apply Fintype.sum_equiv (legalEquiv stages t ha)
  intro x
  apply prod_congr rfl
  intro v _
  apply congrArg₂ (f v)
  · funext s
    rw [emit_shared]
    change _ = read stages t ha (write stages t ha (SwitchFlow.lift _ x)) 0 _
    rw [read_write]; rfl
  · funext s
    rw [receive_shared]
    change _ = read stages t ha (write stages t ha (SwitchFlow.lift _ x)) _ _
    rw [read_write]
    have prev : (finRotate (m+2)).symm 0 = Fin.last (m+1) :=
      (finRotate _).symm_apply_eq.mpr (finRotate_last' (n:=m+1)).symm
    rw [prev]
    rfl

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
