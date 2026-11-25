import OAI.Computability.IntegerMultiplication.Cone.Loop

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Finset Scale Param Echo IntegerMultiplication.Fourier Cap
variable {source:Type} (n:source→ℕ) (P:Faculty n) (T:P.quality n)
variable (p:source)
abbrev N i := criterion (n p) i
abbrev S i:=modulus (n p) i
abbrev val_ i:= Spot (N n p i)→G (n p)

-- grid actual A/B passes across one dimensional input. compute.
noncomputable section
variable (H:Season (n p))
include T H
variable (i:Direction (n p))
def extend_ (x:val_ n p i) (j : Spot (N n p i)) :=
  ∑ l∈rad (Scale.L (n p)),
    punch (x (Echo.glue (pitch H i) (Fourier.nextSample j l)))
      (P.widen p i j (Fourier.nextSample j l))
def close_ (u:Bool) (x:val_ n p i) (b:Spot (N n p i)) :=
  hair (s:=S n p i) (fun b=>
    ∑ l∈rad (Scale.K (n p)*Scale.J (n p)), let q:= Echo.pk (Scale.K (n p)) (Scale.J (n p)) b l
                                           punch (x (Fourier.pick (S n p i) (N n p i) (pitch H i) q))
                                             (P.narrow u p i b q)) b

omit T H in
private theorem charge {α : Type} (s:Finset α) (a:ℕ) (h : s.card ≤ a) :
    (s.card:ℝ)≤a := by exact_mod_cast h
omit T in
theorem size_A:
    ((rad (Scale.L (n p))).card:ℝ) ≤ wash (n p) := by
  rw [rad_card]; push_cast; exact careA H (cursor _)
omit T in
theorem size_B:
    ((rad (Scale.K (n p)*Scale.J (n p))).card:ℝ) ≤ wash (n p) := by
  rw [rad_card]; push_cast; exact careB H (cursor _)
structure Row {t:ℕ} {n:ℕ} (r: Local t)
    (x: (Spot t→G n)→Spot t→G n) : Prop where
  value B f (P:1≤B) (Q:B≤hi n 800) (t:Bound (look n ∘ f) B) :
    Bound (look n ∘ x f) (B*flare n)
  quality B f (P:1≤B) (Q:B≤hi n 800) (t:Bound (look n ∘ f) B) :
    Gap (look n ∘ x f)
      (page r (look n ∘ f)) (err n*(B*flare n))
  ideal B f (P:0≤B) (t:Bound f B) :
    Bound (page r f) (B*flare n)

omit T H in
private theorem ward {α:Type} (s:Finset α) (x w:α→ℂ){B:ℝ}
    (P:(s.card:ℝ) ≤ wash (n p))
    (t:∀ i∈s,‖w i‖≤wash (n p))
    (q:∀ i∈s,‖x i‖≤B)
    (w₀:0≤B):
    ‖∑ i∈s,w i*x i‖≤ B*flare (n p) := by
  have h:= wash1 (n p)
  have v:= norm_sum_le_of_le s (f:= fun i=>w i*x i) (n:=fun _=>wash (n p)*B) (fun i e=> by
    simp only [norm_mul]; exact mul_le_mul (t i e) (q i e) (norm_nonneg _) (by linarith))
  rw [sum_const,nsmul_eq_mul] at v
  unfold flare; rw [← wash_sq]
  nlinarith [mul_le_mul_of_nonneg_right P (show 0≤wash (n p)*B by positivity),
    mul_nonneg w₀ (sq_nonneg (wash (n p)))]

theorem a_rule :
    Row (Growing (n p) H i) (extend_ n P p H i) := by
  let I := n p
  let A := rad (Scale.L I)
  have evolve (x:val_ n p i) (j : Spot (N n p i)) (B:ℝ)
      (X:Bound (look I∘ x) B) (v:1≤B)(h:B≤hi I 800):
      ‖look I (extend_ n P p H i x j)‖≤ B*flare I ∧
      ‖look I (extend_ n P p H i x j) - Echo.page (Growing I H i) (look I ∘ x) j‖≤ err I*(B*flare I) := by
    let z (l:ℤ):=nextSample (s:=S n p i) j l
    let b (l:ℤ):= Echo.glue (pitch H i) (z l)
    let c (l:ℤ):=win (Scale.D I i) j (z l)
    let E (l:ℤ):=P.widen p i j (z l)
    have H1:= ember A (fun l=>x (b l)) E c v h (fun i _=>X _) (fun i _=>(win_bound ..).trans (wash1 _))
      (fun i _=> T.A _ ..) (size_A n p H)
    have a : page (Growing I H i) (look I ∘ x) j=∑ l∈A,c l*look I (x (b l)) :=
      page_A (pitch H i) (Scale.D I i) (Scale.L I) (look I ∘ x) j
    -- cheap conv only given selected argument
    exact ⟨H1.1,le_trans (le_of_eq (congrArg (fun g=> ‖look I (extend_ n P p H i x j)-g‖) a)) H1.2⟩
  refine {
    value:=fun B f i j t w=> (evolve f w B t i j).1
    quality:=fun B f i j t w=> (evolve f w B t i j).2
    ideal:=?_ }
  intro B f x t j
  unfold Growing
  rw [page_A]
  let a:Finset ℤ:=rad (Scale.L (n p))
  let v (u:ℤ):=nextSample (s:=S n p i) j u
  let z (u:ℤ):=win (D (n p) i) j (v u)
  exact ward n p a (fun l=>f (glue (pitch H i) (v l))) z (size_A n p H)
    (fun _ _=> (win_bound ..).trans (wash1 _)) (fun _ _=> t _) x

theorem b_rule (u:Bool):
    Row (Closing (n p) u H i) (close_ n P p H i u) := by
  let I:=n p
  let R:=rad (Scale.K I * Scale.J I)
  let A (b:Spot (S n p i)) (l:ℤ):= Echo.pk (Scale.K I) (Scale.J I) b l
  let Y b l:=Garden.climate u (mixTable (N n p i) (D I i) (nhood (Scale.J I)) (Scale.K I) b (A b l)) (S n p i)
  let v b l:= pick (S n p i) (N n p i) (pitch H i) (A b l)
  have E (x:val_ n p i) (B:ℝ) (s:Bound (look I ∘ x) B) (w:1≤B) (t:B≤hi I 800)
      (b:Spot (S n p i)):
      let U := ∑ l∈R,punch (x (v b l)) (P.narrow u p i b (A b l))
      ‖look I U‖≤ B*flare I ∧
        ‖look I U-∑ l∈R,Y b l*(look I ∘ x) (v b l)‖≤err I*(B*flare I) :=
    ember R (fun l=> x (v b l)) (fun l=> P.narrow u p i b (A b l)) (Y b)
      w t (fun l _=> s _) (fun l _=> careWeights H i u b _) (fun l _=> T.B _ _ ..) (size_B n p H)
  constructor
  · intro B f V Q t a
    unfold Function.comp close_ hair; split
    next h=> exact (E f B t V Q ⟨a.val,h⟩).1
    simp only [lookingZero,norm_zero]
    exact mul_nonneg (by linarith) (by linarith [flare1 (n p)])
  · intro B f S_ Q t a
    unfold Function.comp Closing close_
    rw [page_B]
    unfold hair; split
    next h=> exact (E f B t S_ Q ⟨a.val,h⟩).2
    simp only [lookingZero,sub_self,norm_zero]
    exact mul_nonneg (invp _).le (mul_nonneg (by linarith) (by linarith [flare1 (n p)]))
  intro B f V t a
  unfold Closing; rw [page_B]; unfold hair; split
  next h =>
    exact ward n p R (fun l=> f (v ⟨a.val,h⟩ l)) (Y ⟨a.val,h⟩) (size_B n p H)
      (fun l _=> careWeights H ..) (fun _ _=>t _) V
  simp only [norm_zero]; exact mul_nonneg V (by linarith [flare1 (n p)])
end
end Cone

end IntegerMultiplication
end Computability
end OAI
