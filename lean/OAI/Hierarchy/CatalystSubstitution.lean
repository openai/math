import OAI.Hierarchy.CatalystSubstitutionLocal
import OAI.Hierarchy.CatalystSubstitutionNetwork
import OAI.Hierarchy.GridSum
import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.CorrectionBenchmark

namespace OAI
/-! # Substitution of an approximate tensor into an open oracle occurrence

The old-error term attaches fresh identity wires. The replacement-error term
contracts the opened circuit at the origin. For each of these two local maps,
transporting the newly exposed bits accounts for the other through budget.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open LinearAlgebra.SpectralBooks SiteTensor Catalyst
open scoped Classical BigOperators

variable {k p q : ℕ} {F : Type*} [Field F]

private def Good (c : Fin k → ℕ) (u : Wire c × Bool → Bool) : Prop :=
  ∀ w, u (w,false) = u (w,true)

private theorem ideal_packed (b c : Fin k → ℕ) (g : (Fin p → Bool) → F)
    (x : Port p (fun j => b j+c j) → Bool) :
    ideal (fun j => b j+c j) g x =
      if Good c (x ∘ newPort b c) then ideal b g (x ∘ oldPort b c) else 0 := by
  have wires : Good (fun j => b j+c j) (x ∘ Sum.inr) ↔
      Good b (x ∘ oldPort b c ∘ Sum.inr) ∧ Good c (x ∘ newPort b c) := by
    constructor
    · intro h; exact ⟨fun w => h (wireEquiv b c (.inl w)),fun w => h (wireEquiv b c (.inr w))⟩
    · rintro ⟨a,n⟩ w
      obtain ⟨t,rfl⟩ := (wireEquiv b c).surjective w
      cases t with
      | inl w => exact a w
      | inr w => exact n w
  by_cases hb : Good b (x ∘ oldPort b c ∘ Sum.inr)
  · by_cases hc : Good c (x ∘ newPort b c)
    · have hg := wires.mpr ⟨hb,hc⟩
      unfold ideal
      simp only [Good,Function.comp_apply] at hb hc hg ⊢
      rw [ite_eq_left hg,ite_eq_left hc,ite_eq_left hb]; rfl
    · have hg : ¬Good (fun j=>b j+c j) (x ∘ Sum.inr) := fun h=>hc (wires.mp h).2
      unfold ideal
      simp only [Good,Function.comp_apply] at hg hc ⊢
      rw [ite_eq_right hg,ite_eq_right hc]
  · have hg : ¬Good (fun j=>b j+c j) (x ∘ Sum.inr) := fun h=>hb (wires.mp h).1
    by_cases hc : Good c (x ∘ newPort b c)
    · unfold ideal
      simp only [Good,Function.comp_apply] at hb hc hg ⊢
      rw [ite_eq_right hg,ite_eq_left hc,ite_eq_right hb]
    · unfold ideal
      simp only [Good,Function.comp_apply] at hg hc ⊢
      rw [ite_eq_right hg,ite_eq_right hc]

private def oldKernel (c : Fin k → ℕ) (x : Port p c → Bool) (h : Fin p → Bool) : F :=
  if h = x ∘ Sum.inl then (if Good c (x ∘ Sum.inr) then 1 else 0) else 0

private def liftOld (b c : Fin k → ℕ) :=
  localAction (flippedEquiv (p:=p) b c) (oldKernel (F:=F) c)

private theorem liftOld_apply (b c : Fin k → ℕ) (v : (Port p b → Bool) → F)
    (x : Port p (fun j => b j+c j) → Bool) :
    liftOld b c v x = if Good c (x ∘ newPort b c) then v (x ∘ oldPort b c) else 0 := by
  change (∑ h, (if h = (fun i => x (.inl i)) then
    (if Good c (x ∘ newPort b c) then 1 else 0) else 0) *
    v (Sum.elim h (fun i => x (oldPort b c (.inr i))))) = _
  have pack : Sum.elim (fun i => x (.inl i)) (fun i => x (oldPort b c (.inr i))) = x ∘ oldPort b c := by
    funext i; cases i <;> rfl
  simp only [ite_mul,zero_mul,one_mul,Fintype.sum_ite_eq',pack]

private theorem port_cost (c : Fin k → ℕ) :
    ∑ l : Port p c, dist (sites c l) 0 = 2*∑ j, (c j : ℝ) := by
  have d (i : Wire c × Bool) : dist (sites (p:=p) c (.inr i)) 0 = 1 := by
    rcases i with ⟨⟨j,t⟩,s⟩
    cases s <;> simp [sites,dist_zero_right]
  have z (i : Fin p) : dist (sites c (.inl i)) 0 = 0 := dist_self _
  simp only [Fintype.sum_sum_type,z,d,Finset.sum_const_zero,zero_add,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,
    Nat.cast_ofNat,CorrectionBenchmark.card_wires]; ring

private theorem inputSites (c : Fin k → ℕ) :
    Sum.elim (fun _ : Fin q => 0) (fun i => sites (p:=q) c (.inr i)) = sites c := by
  funext i; cases i <;> rfl

private theorem liftOld_price (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (b c : Fin k → ℕ) (v : (Port p b → Bool) → F) :
    P.price (bitTensor (liftOld b c v)) (sites (fun j => b j+c j)) ≤
      P.price (bitTensor v) (sites b) + 2*∑ j, (c j : ℝ) := by
  have h := price_move_localAction P (flippedEquiv (p:=p) b c) (oldKernel (F:=F) c) v
    (sites (fun j => b j+c j)) 0 (fun i => sites (p:=p) b (.inr i)) (fun _ => rfl)
  have sl (l : Port p c) : sites _ (flippedEquiv b c (.inl l)) = sites c l := by
    rcases l with i | ⟨⟨j,t⟩,s⟩ <;> rfl
  simpa only [liftOld,sl,inputSites,port_cost] using h

private theorem plugError_price (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (b c : Fin k → ℕ) (K : (Port p b → Bool) → (Fin q → Bool) → F)
    (v : (Port q c → Bool) → F) :
    P.price (bitTensor (localAction (portEquiv b c) K v)) (sites (fun j => b j+c j)) ≤
      P.price (bitTensor v) (sites c) + 2*∑ j, (b j : ℝ) := by
  have h := price_move_localAction P (portEquiv b c) K v (sites (fun j => b j+c j)) 0
    (fun i => sites (p:=q) c (.inr i)) (fun _ => rfl)
  have sl (l : Port p b) : sites _ (portEquiv b c (.inl l)) = sites b l := by
    rcases l with i | ⟨⟨j,t⟩,s⟩ <;> rfl
  simpa only [sl,inputSites,port_cost] using h

private theorem split_error (C : Context F k p q) (X : Approximation F k q)
    (f : (Fin q → Bool) → F) (g : (Fin p → Bool) → F) :
    ((approxPlug C X).error g).coeff =
      liftOld C.width X.width ((exactPlug C f).error g).coeff +
      localAction (portEquiv C.width X.width) C.coeff (X.error f).coeff := by
  change (fun x : Port p (fun j => C.width j+X.width j) → Bool =>
    (approxPlug C X).coeff x - ideal (fun j => C.width j+X.width j) g x) = _
  funext x
  change (approxPlug C X).coeff x - ideal (fun j => C.width j+X.width j) g x =
    liftOld C.width X.width (fun y : Port p C.width → Bool => (exactPlug C f).coeff y - ideal C.width g y) x +
      localAction (portEquiv C.width X.width) C.coeff
        (fun y : Port q X.width → Bool => X.coeff y - ideal X.width f y) x
  rw [approxPlug_coeff,ideal_packed,liftOld_apply]
  rw [exactPlug_coeff]
  unfold localAction
  simp only [portEquiv_inl,portEquiv_inr,mul_sub,
    Finset.sum_sub_distrib]
  by_cases h : Good X.width (x ∘ newPort C.width X.width)
  · simp only [ite_eq_left h]
    have hi (t : Fin q → Bool) : ideal X.width f (Sum.elim t (x ∘ newPort C.width X.width)) = f t :=
      ite_eq_left h
    simp only [Function.comp_def] at hi ⊢
    simp only [hi]
    ring
  · simp only [ite_eq_right h]
    have hi (t : Fin q → Bool) : ideal X.width f (Sum.elim t (x ∘ newPort C.width X.width)) = 0 :=
      ite_eq_right h
    simp only [Function.comp_def] at hi ⊢
    simp [hi]

/-- The gap under a single occurrence substitution, for arbitrary call arity,
opening context, and numbers of old and replacement wires in each direction. -/
theorem approxPlug_gap (C : Context F k p q) (X : Approximation F k q)
    {f : (Fin q → Bool) → F} {g : (Fin p → Bool) → F} {D d : ℝ}
    (hg : (exactPlug C f).Gap g D) (hx : X.Gap f d) :
    (approxPlug C X).Gap g (min D d - 2*(k:ℝ)) := by
  intro P
  let b := C.width
  let c := X.width
  let a := liftOld b c ((exactPlug C f).error g).coeff
  let n := localAction (portEquiv b c) C.coeff (X.error f).coeff
  let B := 2*∑ j, (b j : ℝ)
  let N := 2*∑ j, (c j : ℝ)
  have ha (nz : a ≠ 0) : P.price (bitTensor a) (sites (fun j => b j+c j)) ≤ B+N-min D d := by
    have nv : ((exactPlug C f).error g).coeff ≠ 0 := by
      intro h; apply nz; dsimp only [a,liftOld]; rw [h]
      exact localAction_zero (flippedEquiv (p:=p) b c) (oldKernel (F:=F) c)
    have bound := (hg P).resolve_left nv
    have move := liftOld_price P b c ((exactPlug C f).error g).coeff
    change P.price (bitTensor ((exactPlug C f).error g).coeff) (sites b) ≤ B-D at bound
    change P.price (bitTensor a) _ ≤ P.price (bitTensor ((exactPlug C f).error g).coeff) (sites b)+N at move
    linarith [min_le_left D d]
  have hn (nz : n ≠ 0) : P.price (bitTensor n) (sites (fun j => b j+c j)) ≤ B+N-min D d := by
    have nv : (X.error f).coeff ≠ 0 := by
      intro h; apply nz; dsimp only [n]; rw [h]
      exact localAction_zero (portEquiv (p:=p) b c) C.coeff
    have bound := (hx P).resolve_left nv
    have move := plugError_price P b c C.coeff (X.error f).coeff
    change P.price (bitTensor (X.error f).coeff) (sites c) ≤ N-d at bound
    change P.price (bitTensor n) _ ≤ P.price (bitTensor (X.error f).coeff) (sites c)+B at move
    linarith [min_le_right D d]
  have split : ((approxPlug C X).error g).coeff = a+n := split_error C X f g
  by_cases h0 : a+n = 0
  · exact Or.inl (split.trans h0)
  right
  have budget : 2*(∑ j, (((approxPlug C X).width j : ℕ):ℝ)) = B+N := by
    simp [approxPlug,b,c,B,N,Finset.sum_add_distrib,mul_add]
  rw [budget]
  change P.price (bitTensor ((approxPlug C X).error g).coeff) (sites (fun j => b j+c j)) ≤ _
  rw [split]
  change P.price (bitTensor (I:=Port p (fun j => b j+c j)) (a+n)) (sites (fun j => b j+c j)) ≤
    B+N-(min D d - 2*(k:ℝ))
  cases k with
  | zero =>
    have collapse (v : (Port p (fun j => b j+c j) → Bool) → F) : P.price (bitTensor v) (sites _) = 0 := by
      have same : sites (p:=p) (fun j => b j+c j) = (fun _ => (0 : EuclideanSpace ℝ (Fin 0))) := by
        funext i
        exact PiLp.ext (fun j => Fin.elim0 j)
      rw [same,P.collapsed]
    rw [collapse (a+n)]
    by_cases az : a = 0
    · have H := hn (by simpa [az] using h0); rw [collapse] at H; simpa using H
    · have H := ha az; rw [collapse] at H; simpa using H
  | succ k =>
    let : Nontrivial (CorrectionFrame.Location (k+1)) :=
      ⟨⟨none, some ((0 : Fin (k+1)),false), by intro h; cases h⟩⟩
    let term (u : Bool) := if u then a else n
    have sum_eq : ∑ u, term u = a+n := by simp [term]
    obtain ⟨u,un,bound⟩ := GridSum.price_sum P (CorrectionFrame.frame (k+1)) CorrectionFrame.location
      term (sum_eq ▸ h0)
    rw [sum_eq,← CorrectionFrame.sites_eq] at bound
    have scale := CorrectionFrame.scale_le P (k:=k+1)
    have hu : P.price (bitTensor (term u)) (sites (fun j => b j+c j)) ≤ B+N-min D d := by
      cases u <;> simp [term] at un ⊢ <;> first | exact ha un | exact hn un
    simp only [Fintype.card_bool,Nat.cast_ofNat,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
      mul_one] at bound
    change P.price (bitTensor (a+n)) _ ≤ P.price (bitTensor (term u)) _ + _ at bound
    exact bound.trans ((add_le_add hu scale).trans (by linarith))

end Hierarchy.CatalystSubstitution

end
end OAI
