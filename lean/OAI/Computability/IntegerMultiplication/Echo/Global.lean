import OAI.Computability.IntegerMultiplication.Echo.Sample

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Echo
open Finset Scale Param IntegerMultiplication.Fourier Cap
open scoped ComplexConjugate
abbrev modulus (n:ℕ) : Cap.Bounds (lanes n):= fun i=>moduli n i
abbrev criterion (n:ℕ) : Cap.Bounds (lanes n):= fun i=> side n i
variable {n:ℕ} (h:Season n)
include h
theorem lengths_ (i:Direction n) :
    modulus n i ≤ criterion n i := (h.upper i).1
abbrev pitch (i:Direction n) := lengths_ h i

noncomputable def Growing (n:ℕ) (h:Season n) : Square (criterion n) :=
  fun i=> Echo.growing (pitch h i) (D n i) (L n)
noncomputable def Mounting (n:ℕ) (u:Bool) : Square (criterion n) :=
  fun i=> Echo.mounting (modulus n i) u
noncomputable def Closing (n:ℕ) (u:Bool) (h:Season n) : Square (criterion n) :=
  fun i=> Echo.closing (pitch h i) (D n i) (Scale.J n) (Scale.K n) u
noncomputable def desired (u:Bool) (v:Along (criterion n)) : Along (criterion n) :=
  Cap.strand (criterion n) (Closing n u h)
    (strand (criterion n) (Mounting n u)
      (strand (criterion n) (Growing n h) v))
noncomputable def Exact (n:ℕ) (u:Bool) (v:Along (criterion n)): Along (criterion n):=
  strand (criterion n) (fun i=> ideal (s:=modulus n i) (criterion n i) u) v

theorem wished (u) (v) :
    desired h u v=
      strand (criterion n) (fun i=> port (pitch h i) (D n i) (L n) (J n) (K n) u) v := by
  unfold desired
  let s:=criterion n
  have q (A B : Square s) (x:Along s):
      strand s A (strand s B x)=strand s (fun i=>after (A i) (B i)) x :=
    funext (strand_comp s A B x)
  rw [q (Mounting n u),q (Closing n u h)]; rfl

-- local entry error
omit h in
private noncomputable def unit {t:ℕ}(j:Spot t) (i:Spot t):ℂ := if i=j then 1 else 0
omit h in
theorem tests {t} (k : Local t) (j i):
    page k (unit j) i=k i j := by simp [page,unit]
theorem nearly (i:Direction n) (u) (a b:Spot (criterion n i)):
    ‖port (pitch h i) (D n i) (L n) (Scale.J n) (Scale.K n) u a b -
      ideal (s:=modulus n i) (criterion n i) u a b‖ ≤ err n := by
  let s:=modulus n i
  let t:=criterion n i
  let X U:=port (pitch h i) (D n i) (L n) (Scale.J n) (Scale.K n) U
  let Y U:=ideal (t:=t) (s:=s) t U
  have B : ‖X false a b - Y false a b‖≤ err n := by
    unfold X Y
    rw [← tests (port _ _ _ _ _ _) b a,← tests (ideal _ _) b a,
      patience (hk:=(h.grass i).2.1),page_I (pitch h i)]
    simp only [Bool.cond_false,div_one]
    unfold hair; split
    next p =>
      let U := unit b ∘ glue (pitch h i)
      have q : Bound U 1 := by intro x; unfold U Function.comp unit; split <;> simp
      let V:Spot s := ⟨a.val,p⟩
      exact ((h.error i (pitch h i) q zero_le_one) V).trans (by simp)
    simp [Scale.invp n |>.le]
  cases u with
  | false=>exact B
  | true=>
    rw [twin,brothers,← sub_div,← map_sub,norm_div,Complex.norm_conj] -- Complex.norm_conj
    apply le_trans _ B
    have v : 1≤ s := Nat.pos_of_ne_zero (NeZero.ne _)
    apply div_le_self (norm_nonneg _)
    rw [Complex.norm_natCast]; exact_mod_cast v

omit h in
theorem consts_n (i:Direction n) (u:Bool) (a b:Spot (criterion n i)):
    ‖ideal (s:=modulus n i) (criterion n i) u a b‖≤1 := by
  unfold ideal hair; split
  · dsimp only; split
    · rw [norm_div]
      have t : ∀ q,∀ v j : Spot (modulus n i), ‖kernel q v j‖=1 := fun q i j=>phase_norm .. -- i shadow
      rw [t]
      have h:1≤ modulus n i:= Nat.pos_of_ne_zero (NeZero.ne _)
      cases u
      · simp
      simp only [Bool.cond_true,Complex.norm_natCast]
      exact div_le_self zero_le_one (by exact_mod_cast h)
    simp
  simp

-- normalized exact form
noncomputable def source (n:ℕ) (u:Bool)(x:Along (modulus n)) :=
  fun z=> sing (modulus n) (fun i=>bif u then -(criterion n i:ℤ) else (criterion n i:ℤ)) x z /
    (bif u then (space (modulus n):ℂ) else 1)
theorem exterior (f:Along (modulus n)) (u:Bool):
    Exact n u (shell f)=shell (source n u f) := by
  let k:Square (modulus n) := fun i x y=>
    kernel (bif u then -(criterion n i:ℤ) else (criterion n i:ℤ)) x y /
      (bif u then ((modulus n i):ℂ) else 1)
  have eq : Exact n u (shell f) = shell (m:=criterion n) (strand _ k f) :=
    extension (n:=modulus n) (m:=criterion n) (fun i=>pitch h i) k f
  rw [eq]
  congr 1
  funext i
  unfold k strand source sing; unfold strand
  classical
  cases u
  · simp
  simp only [Bool.cond_true]
  rw [Finset.sum_div]
  refine sum_congr rfl fun j _=> ?_
  rw [prod_div_distrib]
  unfold space modulus
  rw [Nat.cast_prod]
  ring

omit h in
theorem strip_line {B : ℝ} (x:Along (modulus n)):
    Bound x B→Bound (shell x (m:=criterion n)) B := by
  classical
  intro t i
  have e : 0≤ B := by
    have p : Nonempty (Vector_ (modulus n)) := ⟨fun _ => 0⟩
    exact (norm_nonneg _).trans (t (Classical.choice p))
  unfold shell; split <;> first | exact t _ | simpa only [norm_zero] using e

end Echo

end IntegerMultiplication
end Computability
end OAI
