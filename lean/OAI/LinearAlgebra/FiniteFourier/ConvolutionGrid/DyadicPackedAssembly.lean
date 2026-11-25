import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridPacking
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyTransforms
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMatrix

/-! # From multiplication on CRT grid coefficients to an open convolution

Packing uses the two monogenic coordinates of a jet followed by the CRT address.
The internal transforms use the CRT address first and the jet coordinates in operand
order. The two changes of wire labels are free. -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Module Polynomial
open scoped BigOperators Classical

noncomputable section

variable {R S G B : Type*} [CommRing R] [CommRing S] [AddCommMonoid G] [Fintype G] [Fintype B]
  {n e r N a d : ℕ} {H : B → ℕ}

/-- Run the grid transforms on their jet arrays, with the mixed-radix input/output
order and the three-child decoder order required by the open convolution constructor. -/
theorem exists_openConvolution_of_grid (φ : R →+* S) (η : S)
    (hcoord : Function.Injective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (M : S[X]) (jet : ∀ b, JetCircuitsOver φ η M e (H b))
    (b : Basis (Fin e × Fin r) S (JetQuotient M r)) (u v : JetQuotient M r)
    (hb : ∀ i j, b (i,j) = u^i.val*v^j.val)
    (hdec : ∀ (x : (Fin r × Fin e) × Fin 2 → R) (z : JetQuotient M r),
      jetOperandValue φ η M x = z ↔
        ∀ i : Fin e × Fin r, QuadraticDescent.decode φ η (fun j => x ((j.1.2,j.1.1),j.2)) i =
          b.repr z i)
    (E : Fin N ≃ G) (g : G) (hE : ∀ k : Fin N, E k = k.val • g)
    (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N)
    (q : Circuit R (G × ((Fin r × Fin e) × Fin 2)) (JetBlockInput (fun _ : B => e) H) a)
    (t : Circuit R (JetBlockInput (fun _ : B => e) H) (G × ((Fin r × Fin e) × Fin 2)) d)
    (f : (G → JetQuotient M r) → ∀ b, JetQuotient M (H b))
    (j : (∀ b, JetQuotient M (H b)) → G → JetQuotient M r)
    (hf : ∀ x b, jetBlockValue φ η (fun _ => M) (q.eval x) b = f (jetOperandArray φ η M x) b)
    (hj : ∀ x, jetOperandArray φ η M (t.eval x) = j (jetBlockValue φ η (fun _ => M) x))
    (hh : ∀ x y, j (f x * f y) = cyclicProduct x y) :
    ∃ p : OpenConvolution R n (B × Fin 3) (jetBlockLength (fun _ => e) H), p.RealizesMultiple 1 ∧
      p.linearCost ≤ 2*a+d+e*r*N+∑ b, JetAssembly.blockCost e (H b) := by
  let packed := packingBasis b E
  let wire (t : G × ((Fin r × Fin e) × Fin 2)) := ((t.2.1.2,t.2.1.1,E.symm t.1),t.2.2)
  let unWire (t : (Fin e × Fin r × Fin N) × Fin 2) := (E t.1.2.2,(t.1.2.1,t.1.1),t.2)
  let q' := q.rewire (fun i => (1,wire i)) (fun i => (1,i))
  let uWire (i : JetBlockInput (fun _ : B => e) H) : JetBlockOutput (fun _ => e) H :=
    ⟨i.1,(i.2.2,i.2.1.1),i.2.1.2⟩
  let t' := t.rewire (fun i => (1,uWire i)) (fun i => (1,unWire i))
  refine exists_packedOpenConvolution φ η hcoord (fun _ => M) jet packed
    (AddMonoidAlgebra.single 0 u) (AddMonoidAlgebra.single 0 v) (AddMonoidAlgebra.single g 1)
    ?_ he hr hcap q' t' ?_
  · intro i
    rw [show packed i = _ from packingBasis_apply b E i, hb, hE]
    simp [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  intro X Y x y hx hy z hz i
  have row (X : AddMonoidAlgebra (JetQuotient M r) G) (x) (hx : ∀ i,
      QuadraticDescent.decode φ η x i = packed.repr X i) :
      jetOperandArray φ η M (x ∘ wire) = X.coeff := by
    funext k
    apply (hdec _ _).2
    intro t
    have hr := hx (t.1,t.2,E.symm k)
    simpa only [packed, packingBasis_repr, E.apply_symm_apply, QuadraticDescent.decode, wire,
      Function.comp_apply] using hr
  have readInput (x) (i : B) : jetBlockValue φ η (fun _ => M) (q'.eval x) i =
      f (jetOperandArray φ η M (x ∘ wire)) i := by
    have hq : q'.eval x = q.eval (x ∘ wire) := by
      funext k
      simp [q', Circuit.eval_rewire, Function.comp_def]
    rw [hq, hf]
  have hz' : jetBlockValue φ η (fun _ => M) (z ∘ uWire) = f X.coeff * f Y.coeff := by
    funext b
    have his := hz b
    rw [readInput, readInput, row _ _ hx, row _ _ hy] at his
    rw [jetOutputValueOver_eq_jetQuotientValue] at his
    exact his
  have ret := hj (z ∘ uWire)
  rw [hz', hh, ← coeff_mul_cyclicProduct] at ret
  have hr := (hdec _ _).1 (congrFun ret (E i.2.2)) (i.1,i.2.1)
  simpa only [packed, packingBasis_repr, t', unWire, QuadraticDescent.decode, Circuit.eval_rewire,
    Function.comp_def, one_mul] using hr

end
end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
