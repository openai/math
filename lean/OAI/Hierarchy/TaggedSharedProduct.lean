import OAI.Hierarchy.CatalystSubstitutionTrace
import OAI.Hierarchy.TaggedSharedWiring

namespace OAI
/-! # Products of catalyst-bearing tests with shared exposed data

Each component reads its own designated data pins. The physical product reuses
their addresses. Opening a component for the price proof yields an equality
constraint on its entire data word, including repeated addresses.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution.SharedProduct
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p q : ℕ}

private def mask (B : Approximation F k p) (f : (Fin p → Bool) → F) : Approximation F k p :=
  tableApprox B.width (fun x : Port p B.width → Bool => B.coeff x * f (x ∘ Sum.inl))

@[simp] private theorem mask_coeff (B : Approximation F k p) (f : (Fin p → Bool) → F)
    (x : Port p B.width → Bool) : (mask B f).coeff x = B.coeff x * f (x ∘ Sum.inl) :=
  tableApprox_coeff _ _ x

private def cut (a : Fin q → Fin p) (B : Approximation F k p) (f : (Fin p → Bool) → F) :
    Context F k p q :=
  ⟨B.width,TypedWiring.localTable fun x : Port p B.width ⊕ Fin q → Bool =>
    if x ∘ Sum.inr = x ∘ Sum.inl ∘ Sum.inl ∘ a then
      B.coeff (x ∘ Sum.inl) * f (x ∘ Sum.inl ∘ Sum.inl) else 0⟩

private theorem cut_coeff (a : Fin q → Fin p) (B : Approximation F k p)
    (f : (Fin p → Bool) → F) (x : Port p B.width → Bool) (b : Fin q → Bool) :
    (cut a B f).coeff x b = if b = x ∘ Sum.inl ∘ a then B.coeff x * f (x ∘ Sum.inl) else 0 := by
  unfold cut Context.coeff
  rw [TypedWiring.localTable_value]
  rfl

private theorem step (a : Fin q → Fin p) (B : Approximation F k p) (X : Approximation F k q)
    (f g : (Fin p → Bool) → F) (t : (Fin q → Bool) → F) {G : ℝ}
    (prev : (mask B (fun x => t (x ∘ a) * f x)).Gap g G) (ok : X.Gap t G) :
    (mask (extend a B X) f).Gap g (G-2*(k:ℝ)) := by
  have h₁ : Agrees (mask B (fun x => t (x ∘ a) * f x)) (exactPlug (cut a B f) t) := by
    refine ⟨rfl,?_⟩
    change ∀ x : Port p B.width → Bool, (mask B (fun x => t (x ∘ a) * f x)).coeff x =
      (exactPlug (cut a B f) t).coeff x
    intro x
    rw [mask_coeff B _ x,exactPlug_coeff (cut a B f) t x]
    simp only [cut_coeff, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Function.comp_assoc]
    ring
  have h₂ : Agrees (approxPlug (cut a B f) X) (mask (extend a B X) f) := by
    refine ⟨rfl,?_⟩
    change ∀ x : Port p (fun j => B.width j+X.width j) → Bool, (approxPlug (cut a B f) X).coeff x =
      (mask (extend a B X) f).coeff x
    intro x
    rw [mask_coeff (extend a B X) f x,extend_coeff a B X x,approxPlug_coeff (cut a B f) X x]
    let u : Port p B.width → Bool := x ∘ oldPort B.width X.width
    let v : Wire X.width × Bool → Bool := x ∘ newPort B.width X.width
    let d : Fin q → Bool := x ∘ Sum.inl ∘ a
    let weight := f (x ∘ Sum.inl)
    calc
      _ = ∑ h : Fin q → Bool, (if h=d then B.coeff u*weight else 0)*X.coeff (Sum.elim h v) := by
        apply Finset.sum_congr (by ext h; simp)
        intro h _
        exact congrArg (fun s : F=>s*X.coeff (Sum.elim h v)) (cut_coeff a B f u h)
      _ = _ := by
        simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
        change B.coeff u*weight*X.coeff (Sum.elim d v)=B.coeff u*X.coeff (Sum.elim d v)*weight
        ring
  apply h₂.gap
  simpa only [min_self] using approxPlug_gap (cut a B f) X (h₁.gap prev) ok

variable {ι : Type} [DecidableEq ι] (q' : ι → ℕ) (a : ∀ i, Fin (q' i) → Fin p)
  (X : ∀ i, Approximation F k (q' i)) (t : ∀ i, (Fin (q' i) → Bool) → F)

private theorem accumulate (s : Finset ι) (B : Approximation F k p) :
    ∃ Y : Approximation F k p, Y.size + ∑ i ∈ s, q' i = B.size + ∑ i ∈ s, (X i).size ∧
      ∀ (g : (Fin p → Bool) → F) (G : ℝ),
      (mask B (fun x => ∏ i ∈ s, t i (x ∘ a i))).Gap g G →
      (∀ i ∈ s, (X i).Gap (t i) G) → Y.Gap g (G - 2*(k:ℝ)*(s.card:ℝ)) := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty =>
    refine ⟨B,by simp,fun g G old _ => ?_⟩
    have e : Agrees (mask B (fun x => ∏ i ∈ (∅ : Finset ι), t i (x ∘ a i))) B :=
      ⟨rfl,fun x => by
        change (mask B _).coeff x = B.coeff x
        rw [mask_coeff B _ x]
        simp⟩
    simpa using e.gap old
  | @insert i s hi ih =>
    obtain ⟨Y,size,prices⟩ := ih (extend (a i) B (X i))
    refine ⟨Y,?_,fun g G old calls => ?_⟩
    · rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have bill := extend_size (a i) B (X i)
      omega
    · simp only [Finset.prod_insert hi] at old
      have next := step (a i) B (X i) (fun x => ∏ j ∈ s, t j (x ∘ a j)) g (t i) old
        (calls i (Finset.mem_insert_self ..))
      have out := prices g (G-2*(k:ℝ)) next (fun j hj => Approximation.Gap.mono _ (calls j
        (Finset.mem_insert_of_mem hj)) (by linarith [Nat.cast_nonneg (α:=ℝ) k]))
      convert out using 1
      rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      ring

private def unit : Approximation F k p :=
  ⟨fun _ => 0, ⟨0,0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩

private theorem unit_value (x : Port p (fun _ : Fin k => 0) → Bool) :
    (unit (F:=F)).coeff x = 1 := by
  unfold Approximation.coeff BitNetwork.eval BitNetwork.weight
  change (∑ h : Fin 0 → Bool, ∏ i : Fin 0, (unit (F:=F) (k:=k) (p:=p)).network.factor _ h i) = 1
  rw [Fintype.sum_unique]
  exact Fintype.prod_empty (ι := Fin 0) _

omit [Field F] in
private theorem unit_size : (unit (F:=F) (k:=k) (p:=p)).size = p := by
  change 0+0+Fintype.card (Fin p ⊕ (Wire (fun _ : Fin k => 0) × Bool)) = p
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma]
  simp

/-- Physically join all networks at the named exposed pins. Each slice
replacement contributes its cells, hidden bits, and both catalyst ends. -/
theorem exists_product [Fintype ι] :
    ∃ Y : Approximation F k p, Y.size + ∑ i, q' i = p + ∑ i, (X i).size ∧
      ∀ G : ℝ, (∀ i, (X i).Gap (t i) G) →
        Y.Gap (fun x => ∏ i, t i (x ∘ a i)) (G-2*(k:ℝ)*(Fintype.card ι:ℝ)) := by
  classical
  obtain ⟨Y,size,prices⟩ := accumulate q' a X t Finset.univ unit
  refine ⟨Y,by simpa only [unit_size] using size,fun G h => ?_⟩
  apply prices _ G _ (fun i _ => h i)
  let f : (Fin p → Bool) → F := fun x => ∏ i, t i (x ∘ a i)
  have same (x : Port p (fun _ : Fin k => 0) → Bool) : (mask unit f).coeff x =
      ideal (fun _ : Fin k => 0) f x := by
    have empty (j : Wire (fun _ : Fin k => 0)) : x (.inr (j,false)) = x (.inr (j,true)) :=
      Fin.elim0 j.2
    rw [mask_coeff unit f x,unit_value x,one_mul,ideal,ite_eq_left empty]
    rfl
  intro P
  left
  funext x
  exact sub_eq_zero.mpr (same x)

end Hierarchy.CatalystSubstitution.SharedProduct

end
end OAI
