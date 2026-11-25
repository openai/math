import OAI.LinearAlgebra.FiniteFourier.OpenConvolution

/-! # Bilinear coefficients of open convolution reductions -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R I O M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Run a program on vectors in an arbitrary module using its scalar coefficients. -/
private def moduleValue : {s : ℕ} → Program R I s → (I → M) → Fin s → M
  | _, .nil, _ => Fin.elim0
  | _, .step p g, x =>
    let w := Sum.elim x (moduleValue p x)
    Fin.cases (g.leftCoeff • w g.left + g.rightCoeff • w g.right) (moduleValue p x)

private theorem map_wire (f : M →ₗ[R] R) {s : ℕ} (p : Program R I s) (x : I → M)
    (w : I ⊕ Fin s) : f (Sum.elim x (moduleValue p x) w) =
      Sum.elim (f ∘ x) (p.value (f ∘ x)) w := by
  induction p with
  | nil => cases w with
    | inl => rfl
    | inr j => exact j.elim0
  | step p g ih =>
    cases w with
    | inl => rfl
    | inr j =>
      refine Fin.cases ?_ (fun i => ih (.inr i)) j
      change f (_ • _ + _ • _) = g.eval _
      simp only [map_add, map_smul, smul_eq_mul, ih, BinaryGate.eval]

private def moduleEval {s : ℕ} (p : Circuit R I O s) (x : I → M) (o : O) : M :=
  match p.output o with
  | .zero => 0
  | .scaled c w => c • Sum.elim x (moduleValue p.program x) w

private theorem map_eval (f : M →ₗ[R] R) {s : ℕ} (p : Circuit R I O s) (x : I → M) (o : O) :
    f (moduleEval p x o) = p.eval (f ∘ x) o := by
  cases h : p.output o <;> simp [moduleEval, Circuit.eval, h, Readout.eval, map_wire]

/-- The bilinear map taking two length-`n` vectors to the `k`th product coefficient. -/
def openConvBilinear (R : Type*) [CommRing R] (n : ℕ) (k : Fin (2*n-1)) :
    (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] R :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = k.val then
    (LinearMap.mul R R).compl₁₂ (LinearMap.proj i) (LinearMap.proj j) else 0

@[simp] theorem openConvBilinear_apply (R : Type*) [CommRing R] (n : ℕ)
    (k : Fin (2*n-1)) (x y : Fin n → R) : openConvBilinear R n k x y = openConv R n x y k := by
  simp only [openConvBilinear, openConv, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split <;> rfl

namespace OpenConvolution

variable {n : ℕ} {B : Type*} {len : B → ℕ}

private def inputBlock (p : OpenConvolution R n B len) (b : B) :
    (Fin n → R) →ₗ[R] (Fin (len b) → R) :=
  LinearMap.pi fun i => moduleEval p.input (fun j => LinearMap.proj j) ⟨b, i⟩

private theorem inputBlock_apply (p : OpenConvolution R n B len) (b : B) (x : Fin n → R)
    (i : Fin (len b)) : inputBlock p b x i = p.input.eval x ⟨b, i⟩ :=
  map_eval (LinearMap.applyₗ x) p.input (fun j => LinearMap.proj j) ⟨b, i⟩

/-- The output circuit combines the bilinear forms supplied by each open convolution gate. -/
def bilinear (p : OpenConvolution R n B len) (k : Fin (2*n-1)) :
    (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] R :=
  moduleEval p.output (fun bk =>
    (openConvBilinear R (len bk.1) bk.2).compl₁₂ (inputBlock p bk.1) (inputBlock p bk.1)) k

@[simp] theorem bilinear_apply (p : OpenConvolution R n B len) (k : Fin (2*n-1))
    (x y : Fin n → R) : p.bilinear k x y = p.eval x y k := by
  unfold bilinear eval
  change ((LinearMap.applyₗ y).comp (LinearMap.applyₗ x)) _ = _
  rw [map_eval]
  congr 1
  funext bk
  simp [Function.comp_apply, children, inputBlock_apply, openConv]

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
