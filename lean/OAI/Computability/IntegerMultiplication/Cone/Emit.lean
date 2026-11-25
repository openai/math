import OAI.Computability.IntegerMultiplication.Cone.Pipe

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Echo Scale Cap IntegerMultiplication.Fourier Param
open scoped BigOperators
variable {n:ℕ} (h:Season n)
noncomputable section
def fare (n a:ℕ) := err n*hi n a

theorem fare_p (n a): 0<fare n a := mul_pos (invp _) (by linarith [hi1 n a])
theorem fare_mon (n):Monotone (fare n) := fun _ _ w=>mul_le_mul_of_nonneg_left (hi_mono n w) (invp n).le
theorem fare_due (n) {l:ℕ} (h:l<3000):
    fare n l <1 := by
  unfold fare
  rw [← Scale.stop n]
  apply mul_lt_mul_of_pos_left _ (invp _)
  unfold hi
  apply pow_lt_pow_right₀ (by norm_num)
  exact Nat.mul_lt_mul_of_pos_right h (budget_p n)
theorem fare_pl (n a):
    fare n a+ fare n a ≤ fare n (a+1):=
  calc
    _ = err n*(2*hi n a) := by unfold fare; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (overhead ..) (invp n).le
theorem fare_mul (n a b):fare n a * hi n b=fare n (a+b) := by unfold fare; rw [mul_assoc, heightA]

theorem Flow.harp (a:Farm n→Farm n)(d e:Land n→Land n)
    (p : Flow 500 68 198 a d) (l:ℕ) (v:l≤500)
    (f:Farm n) (b:Bound (array_ n f) (hi n l))
    (z:Gap (d (array_ n f)) (e (array_ n f)) (err n * hi n 4 * hi n l)):
    Bound (array_ n (a f)) (hi n (l+68)) ∧ Gap (array_ n (a f)) (e (array_ n f)) (fare n (l+199)) := by
  have Q:=hi1 n l
  have W:=hi_mono n v
  refine ⟨(p.norm_ (hi n l) Q W f b).mono (le_of_eq (heightA n l 68)), ((p.delta _ Q W f b).trans z).mono ?_⟩
  change fare n l*hi n 198+fare n 4*hi n l ≤_
  rw [fare_mul,fare_mul]
  have s := add_le_add_right (fare_mon n (by omega : 4+l≤l+198)) (fare n (l+198))
  exact s.trans (by simpa [Nat.add_assoc] using fare_pl n (l+198))
-- conclusion for single transform at exponent i.
variable {I:Type} (r:I→ℕ) (z:Faculty r) (T:z.quality r)(i:I)(q:Season (r i))
variable (x:Organ (r i))(A:Angled (r i) x)
include T A
theorem conversion (u:Bool)(l:ℕ)(v:l≤500)(B:Farm (r i))
    (P:Bound (array_ (r i) B) (hi (r i) l)):
    Bound (array_ (r i) (ray r z i q x u B)) (hi (r i) (l+68)) ∧
    Gap (array_ (r i) (ray r z i q x u B)) (Exact (r i) u (array_ (r i) B)) (fare (r i) (l+199)) := by
  have hu1:= travel r z i q T x A u
  let a:= ray r z i q x u
  let d:= desired q u
  exact Flow.harp a d (Exact (r i) u) hu1 l v B P (Echo.alias_ q u _ P (by linarith [hi1 (r i) l]))

-- product stage. two output approximants.
omit T A in
private theorem point {n:ℕ}(x y : G n)(v w:ℂ)
    (P: ‖look n x‖≤hi n 69)(Q:‖look n y‖≤hi n 69)
    (h:‖look n x-v‖≤fare n 200)
    (u:‖look n y-w‖≤fare n 200)
    (G:‖v‖≤hi n 2) :
    ‖look n (punch x y)‖ ≤ hi n 140 ∧
    ‖look n (punch x y)-v*w‖≤ fare n 271 := by
  let X:=look n x
  let Y:=look n y
  let Z:=look n (punch x y)
  let H a:=hi n a
  have z:‖X*Y‖≤H 138 := (le_trans (le_of_eq (norm_mul X Y)) ((mul_le_mul P Q (norm_nonneg _) (by linarith [hi1 n 69])).trans (le_of_eq (heightA n 69 69)))) -- direction
  have a:= Grid.confident (Scale.F n) x y (by
    apply lt_of_le_of_lt ?_ (Scale.model n)
    change ‖X*Y‖*(2:ℝ)^Scale.F n+2 ≤ _
    gcongr
    exact z.trans (hi_mono n (by decide :138≤1000)))
  have v0: 2/(2:ℝ)^Scale.F n ≤ err n := by
    apply le_trans _ (round_n _)
    unfold Star.drop_
    rw [one_div,inv_pow,← div_eq_mul_inv]; gcongr; norm_num
  have j: ‖Z-X*Y‖≤err n:= a.trans v0
  have j0:err n≤1:=err1 n
  change ‖Z‖≤H 140 ∧ ‖Z-v*w‖ ≤ _
  refine ⟨?_,?_⟩
  · have h₀:=norm_add_le (Z-X*Y) (X*Y)
    rw [sub_add_cancel] at h₀
    have p := hi1 n 138
    have v₀ := Scale.overhead 138 n
    have q:H 139 ≤ H 140:= hi_mono n (by decide)
    change 1≤H _ at p
    change 2*H _ ≤ H 139 at v₀
    linarith
  have l: Z-v*w=(Z-X*Y)+((X-v)*Y+v*(Y-w)):=by ring
  rw [l]
  let E:=fare n
  have f1 : ‖(X-v)*Y‖ ≤ E 269 := by
    rw [norm_mul]
    exact (mul_le_mul h Q (norm_nonneg _) (fare_p n _).le).trans (le_of_eq (fare_mul n 200 69))
  have f2 : ‖v*(Y-w)‖ ≤ E 269 := by
    rw [norm_mul,mul_comm]
    exact (mul_le_mul u G (norm_nonneg _) (fare_p n _).le).trans
      ((fare_mul n 200 2).le.trans (fare_mon n (by decide)))
  have t0:= norm_add_le ((X-v)*Y) (v*(Y-w))
  have v₀:= norm_add_le (Z-X*Y) ((X-v)*Y+v*(Y-w))
  have f: E 269+E 269 ≤ E 270 := fare_pl n 269
  have g : E 270+E 270≤ E 271:= fare_pl n 270
  have d: err n≤ E 270:= le_mul_of_one_le_right (invp n).le (hi1 n 270)
  change _ ≤ E 271
  linarith

-- full mathematical answer (before calibration Angled for simultaneous transforms)
abbrev idealPulse (n) (b c : Land n) :=
  Exact n true (fun i=>Exact n false b i* Exact n false c i)
def glint (b c:Farm (r i)):Farm (r i) :=
  ray r z i q x true (fun a=> punch (ray r z i q x false b a) (ray r z i q x false c a))
theorem flash (b c:Farm (r i))
    (B: Bound (array_ (r i) b) (hi (r i) 1))
    (C: Bound (array_ (r i) c) (hi (r i) 1)) :
    Gap (array_ (r i) (glint r z i q x b c))
      (idealPulse (r i) (array_ (r i) b) (array_ (r i) c)) (fare (r i) 340) := by
  let n:=r i
  have h₀:=conversion r z T i q x A
  let P := ray r z i q x false
  let M m:=array_ n (P m)
  let H:=hi n
  let X m:= Exact n false (array_ n m)
  obtain ⟨a,p⟩:= h₀ false 1 (by decide) b B
  obtain ⟨a',p'⟩:= h₀ false 1 (by decide) c C
  let y:Farm (r i):= fun a=>punch (P b a) (P c a)
  let S v : ℂ:= X b v * X c v
  have Q:Bound (X b) (H 2):=
    (Echo.perfection q false (array_ n b) B (by linarith [hi1 n 1])).mono
      (by exact le_of_eq (heightA n 1 1))
  have E v:= point (P b v) (P c v) (X b v) (X c v) (a v) (a' v) (p v) (p' v) (Q v)
  have Y:Bound (array_ n y) (H 140):=fun i=>(E i).1
  have F0:Gap (array_ n y) S (fare n 271):=fun i=>(E i).2
  have M := (h₀ true 140 (by decide) y Y).2
  have U:=perfectionGap q true _ _ F0 (fare_p n _).le
  apply (M.trans U).mono
  rw [mul_comm (hi ..) (fare ..), fare_mul]
  have e := fare_mon (r i) (by decide:271+1≤140+199)
  exact (add_le_add_right e _).trans (by simpa using (fare_pl n (140+199)))

omit T A
theorem final_eps : fare (r i) 340< 1/4 := by
  let n:=r i
  have Q:= fare_due n (by decide:342<3000)
  have e:= fare_pl n 340
  have t:= fare_pl n 341
  change fare n 340 < _
  change fare n _+fare n _≤fare n 341 at e
  change fare n _+fare n _≤fare n 342 at t
  linarith
end
end Cone

end IntegerMultiplication
end Computability
end OAI
