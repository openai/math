import OAI.Computability.IntegerMultiplication.Cone.Rows
import OAI.Computability.IntegerMultiplication.Echo.Shade

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Echo Scale IntegerMultiplication.Fourier Finset Param Cap
variable (n:ℕ)
abbrev Farm := Echo.Grid_ (n:=criterion n) (G n)
abbrev Land := Along (criterion n)
abbrev Curve i := Spot (criterion n i)→G n
abbrev Plans := (i:Direction n)→ Curve n i→Curve n i

noncomputable def array_ (x:Farm n) : Land n:= look n ∘ x
def brisk (p:Plans n) (l:List (Direction n)) (x:Farm n) :=
  l.foldr (fun i x=>Echo.street i (p i) x) x
variable {n}
variable (k:Square (criterion n)) (p:Plans n) (h:∀ i,Row (k i) (p i))
include h
theorem page_gap (i:Direction n) {f g} {B:ℝ} (q:0≤B) (x: Gap f g B) :
    Gap (page (k i) f) (page (k i) g) (B*flare n) := by
  have A:= (h i).ideal B (f-g) q x
  intro a
  unfold page
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  exact A a

private theorem rigging {a:Direction n}
    {x:Farm n} {B:ℝ} (t:1≤B) (v:B≤ hi n 800) (e:Bound (array_ n x) B) :
    Bound (array_ n (Echo.street a (p a) x)) (B*flare n) ∧
    Gap (array_ n (Echo.street a (p a) x))
      (street a (Echo.page (k a)) (array_ n x)) (err n*(B*flare n)) := by
  let f (j:Vector_ (criterion n)) q:= x (alter j a q)
  have g j : Bound (look n ∘ f j) B := fun q=>e _
  exact ⟨fun j=> (h a).value B (f j) t v (g j) (j a),
    fun j=> (h a).quality B (f j) t v (g j) (j a)⟩
private theorem occupation {a:Direction n}
    {x y:Land n} {B:ℝ}(v:0≤B) (e:Gap x y B):
    Gap (Echo.street a (page (k a)) x)
      (Echo.street a (page (k a)) y) (B*flare n) :=
  fun j => page_gap k p h a v (fun i=>e (alter j a i)) (j a)
theorem margin {a:Direction n}
    {x:Land n}{B:ℝ}(v:0≤B)(e:Bound x B):
    Bound (Echo.street a (page (k a)) x) (B*flare n) :=
  fun j=> (h a).ideal _ (fun i=>x (alter j a i)) v (fun _i=>e _) (j a)

theorem odeon (l:List (Direction n)) (x:Farm n) {B:ℝ}
    (t:1≤B) (v:B*(flare n)^l.length ≤ hi n 800)
    (e:Bound (array_ n x) B):
    let f:=l.foldr (fun i z=> Echo.street i (page (k i)) z) (array_ n x)
    let w:=l.foldr (fun i z=> Echo.street i (p i) z) x
    Bound (array_ n w) (B*(flare n)^l.length) ∧
    Gap (array_ n w) f (l.length*err n*(B*(flare n)^l.length)) := by
  have K:= flare1 n
  have B0 : 0≤B:=by linarith -- real
  induction l with
  | nil=> simp [e,Gap.refl]
  | cons i l ih=>
    simp only [List.length_cons,pow_succ, ← mul_assoc] at v
    let R:=B*(flare n)^l.length
    have t0:1 ≤ R := one_le_mul_of_one_le_of_one_le t (one_le_pow₀ K)
    have H : R ≤ hi n 800 := le_trans (le_mul_of_one_le_right (by linarith) K) v
    obtain ⟨a,b⟩:=ih H
    have C:=rigging k p h (a:=i) t0 H a
    have α:(0:ℝ) ≤ l.length*err n* R :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (invp n).le) (by linarith)
    have q:=occupation k p h (a:=i) α b
    simp only [List.foldr_cons,List.length_cons,pow_succ,← mul_assoc]
    refine ⟨C.1,(C.2.trans q).mono ?_⟩
    unfold R
    push_cast; ring_nf; exact le_rfl

theorem assured (x y:Land n) (l:List (Direction n)) {B:ℝ}(v:0≤B)(e:Gap x y B):
    let f (v:Land n):= l.foldr (fun i z=> street i (page (k i)) z) v
    Gap (f x) (f y) (B*(flare n)^l.length) := by
  induction l with
  | nil=>simpa only [List.length_nil,List.foldr_nil,pow_zero,mul_one] using e
  | cons i l ih =>
    have v1 := flare1 n
    have c:0≤ B*flare n^l.length:= by positivity
    simp only [List.foldr_cons,List.length_cons,pow_succ,← mul_assoc]
    exact occupation k p h c ih

abbrev Measure (d:ℕ): List (Fin d) := List.ofFn id
omit h in
theorem measure_specs d:
    (Measure d).length=d ∧ (Measure d).Nodup ∧ ∀ i:Fin d,i∈Measure d := by
  rw [Measure,List.length_ofFn]
  exact ⟨rfl,List.nodup_ofFn.mpr Function.injective_id,fun i=> List.mem_ofFn.mpr ⟨i,rfl⟩⟩

theorem release {B:ℝ}(x:Farm n)(t:1≤B)(z:B≤ hi n 750)(v:Bound (array_ n x) B):
    let Y:= brisk n p (Measure (lanes n)) x
    Bound (array_ n Y) (B*hi n 26) ∧ Gap (array_ n Y)
      (strand (criterion n) k (array_ n x)) (err n*hi n 27*B) := by
  obtain ⟨S,D,E⟩:=measure_specs (lanes n)
  have H (a:ℕ)(v:a≤lanes n): flare n^a≤ hi n 26 :=
    (pow_le_pow_right₀ (flare1 n) v).trans (flareBound n)
  have K := H (Measure (lanes n)).length S.le
  have q:=odeon k p h (Measure (lanes n)) x t ((mul_le_mul z K (pow_nonneg (by linarith [flare1 n]) _) (by linarith)).trans
    ((le_of_eq (heightA n _ _)).trans (hi_mono n (by decide :750+26 ≤800)))) v
  refine ⟨q.1.mono (by gcongr), ?_⟩
  rw [← Echo.schedule k _ _ D E]
  refine q.2.mono ?_
  have t0: lanes n ≤ P n:= Nat.le_self_pow (by decide) _
  have h : (lanes n:ℝ) ≤ hi n 1 := by
    unfold hi
    rw [one_mul]
    exact_mod_cast le_trans t0 (Nat.lt_pow_self (a:=2) (by decide)).le
  rw [S] at *
  calc
    _ ≤ hi n 1*err n*(B*hi n 26) := by
      have v:= (invp n).le; have T:=hi1 n 1; have W:=flare1 n; gcongr
    _ = _ := by rw [show hi n 27 = hi n 1*hi n 26 from (heightA n 1 26).symm];ring
end Cone

end IntegerMultiplication
end Computability
end OAI
