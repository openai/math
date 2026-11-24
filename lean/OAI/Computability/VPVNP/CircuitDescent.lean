import OAI.Computability.VPVNP.Circuits
import OAI.Computability.VPVNP.ScalarDescent

/-!
# Descent without changing the circuit topology

A circuit for a polynomial defined over a base field `k` can replace every scalar
label with a new value in an algebraically closed extension of `k`. This applies
when the original labels belong to an arbitrary extension of `k`. Binary gate
types, wiring, reuse, the designated output and the gate count all persist.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {R S T σ : Type*} {n : ℕ}

private def Ref.scalarLabels : Ref R σ n → List R
  | .const c => [c]
  | .var _ | .gate _ => []

private def Program.scalarLabels : {n : ℕ} → Program R σ n → List R
  | _, .nil => []
  | _, .snoc p _ a b => p.scalarLabels ++ a.scalarLabels ++ b.scalarLabels

/-- All scalar occurrences in a circuit, including an output that is a scalar. -/
def Circuit.scalarLabels (c : Circuit R σ n) : List R :=
  c.program.scalarLabels ++ c.output.scalarLabels

private theorem Ref.subst_inl_comp (r : Ref R σ n) (f : R → S) (g : S → T) :
    (r.subst Sum.inl f).subst Sum.inl g = r.subst Sum.inl (g ∘ f) := by cases r <;> rfl

private theorem Program.subst_inl_comp (p : Program R σ n) (f : R → S) (g : S → T) :
    (p.subst Sum.inl f).subst Sum.inl g = p.subst Sum.inl (g ∘ f) := by
  induction p with
  | nil => rfl
  | snoc p op a b ih => simp only [Program.subst, ih, Ref.subst_inl_comp]

theorem Circuit.mapConstants_comp (c : Circuit R σ n) (f : R → S) (g : S → T) :
    (c.mapConstants f).mapConstants g = c.mapConstants (g ∘ f) := by
  simp only [Circuit.mapConstants, Circuit.subst, Ref.subst_inl_comp, Program.subst_inl_comp]

private theorem Ref.subst_inl_self (r : Ref R σ n) (f : R → R)
    (hf : ∀ x ∈ r.scalarLabels, f x = x) : r.subst Sum.inl f = r := by
  cases r with
  | const x => simp [Ref.subst, hf x (by simp [Ref.scalarLabels])]
  | var | gate => rfl

private theorem Program.subst_inl_self (p : Program R σ n) (f : R → R)
    (hf : ∀ x ∈ p.scalarLabels, f x = x) : p.subst Sum.inl f = p := by
  induction p with
  | nil => rfl
  | snoc p op a b ih =>
    rw [Program.subst, ih (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      a.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx])),
      b.subst_inl_self f (fun x hx ↦ hf x (by simp [Program.scalarLabels, hx]))]

theorem Circuit.mapConstants_self (c : Circuit R σ n) (f : R → R)
    (hf : ∀ x ∈ c.scalarLabels, f x = x) : c.mapConstants f = c := by
  simp only [Circuit.mapConstants, Circuit.subst,
    c.program.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx])),
    c.output.subst_inl_self f (fun x hx ↦ hf x (by simp [Circuit.scalarLabels, hx]))]

/-- Descent of an exact circuit by changing only its scalar labels. The formal target
polynomial is interpreted in the two fields by their respective algebra maps. -/
theorem Circuit.exists_scalar_relabeling {k F K : Type*} [Field k] [Field F] [Field K]
    [Algebra k F] [Algebra k K] [IsAlgClosed K] (c : Circuit F σ n) (p : MvPolynomial σ k)
    (hc : c.polynomial = map (algebraMap k F) p) :
    ∃ relabel : F → K, (c.mapConstants relabel).polynomial = map (algebraMap k K) p := by
  classical
  let labels := c.scalarLabels.toFinset
  let param (v : F) : MvPolynomial (↥labels) k :=
    if h : v ∈ labels then X ⟨v, h⟩ else 0
  let generic := c.mapConstants param
  let values : (↥labels) → F := Subtype.val
  have recover : generic.mapConstants (aeval values).toRingHom = c := by
    rw [Circuit.mapConstants_comp]
    apply Circuit.mapConstants_self
    intro v hv
    have hv' : v ∈ labels := List.mem_toFinset.mpr hv
    simp [param, values, hv']
  have hs : map (aeval values).toRingHom generic.polynomial = map (algebraMap k F) p := by
    rw [← Circuit.map_polynomial, recover, hc]
  obtain ⟨b, hb⟩ := formalOutput_descent (K := K) generic.polynomial p values hs
  exact ⟨(aeval b).toRingHom ∘ param, by
    rw [← Circuit.mapConstants_comp, Circuit.map_polynomial]
    exact hb⟩

end VPVNP
end Computability
end OAI
