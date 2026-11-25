import OAI.Computability.IntegerMultiplication.Grid.Moon
import OAI.Computability.IntegerMultiplication.Dusk.Nerve

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Bits Code Dusk
abbrev Cell := QuadraticAlgebra ℤ (-1) 0
private def wrap {k : ℕ} (x:ℤ) : day k := x
def wrapMap (k : ℕ) : Cell→+* Grain k where
  toFun x := ⟨x.re,x.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_zero' := by ext <;> simp
  map_add' := by intro _ _; ext <;> simp
  map_mul' := by
    intro x y; ext <;> simp

variable {k : ℕ}
def aspect (x : Grain k) : Cell := ⟨Grid.lift x.re,Grid.lift x.im⟩
@[simp] theorem back (x : Grain k) : wrapMap k (aspect x)=x := by
  unfold wrapMap aspect
  ext <;> simp

def tiny (s k : ℕ) (x:Cell) : Prop := |x.re| < (s:ℤ)^k ∧ |x.im|< (s:ℤ)^k
def focus (k : ℕ) (x:Cell) : Prop := tiny 2 k x
theorem recovers (x : Cell) (h : focus k x) :
    aspect (wrapMap k x)=x := by
  unfold aspect wrapMap
  ext
  · exact send_lift h.1
  exact send_lift h.2
theorem aspect_f (x : Grain k) : focus k (aspect x) :=
  ⟨lift_limit x.re,lift_limit x.im⟩
def divA (n:ℕ) (x:Cell) : Cell := ⟨slash n x.re,slash n x.im⟩
abbrev Coef := S × S
def content (x : Coef) : Cell := ⟨whole x.1,whole x.2⟩
def plusG (x : Coef × Coef) : Coef :=
  (Grid.plus (x.1.1,x.2.1),Grid.plus (x.1.2,x.2.2))
@[fun_prop] theorem facile_G : Easy plusG := by unfold plusG; fun_prop
def timesG (x : Coef × Coef) : Coef :=
  let A := Grid.prod (x.1.1,x.2.1)
  let B := Grid.prod (x.1.2,x.2.2)
  let C := Grid.prod (x.1.1,x.2.2)
  let D := Grid.prod (x.1.2,x.2.1)
  (Grid.plus (A,Grid.neg B),Grid.plus (C,D))
@[fun_prop] theorem payG : Charming timesG := by
  have t := smooth easy_plus
  have u := smooth easy_neg
  unfold timesG
  fun_prop

theorem key_P (x y : Coef) : content (plusG (x,y))=content x+content y := by
  unfold content plusG; ext <;> (exact plus_v ..) -- simp no progress
theorem key_M (x y : Coef) : content (timesG (x,y))=content x*content y := by
  unfold content timesG; ext
  · simp [plus_v,prod_exact,neg_r]
  simp [plus_v,prod_exact]

def disp (x : Dusk.Pair) : Coef := (pull x.1,pull x.2)
def spell (x : Coef) : Dusk.Pair := (insert x.1,insert x.2)
def rest (x : Tally× Coef) : Coef :=
  (divpow (x.1,x.2.1),divpow (x.1,x.2.2))
def fit (x : Tally× Coef) : Coef :=
  (truncate0 (x.1,x.2.1),truncate0 (x.1,x.2.2))
def Width (w:ℕ) (x:Coef) := dept x.1=w ∧ dept x.2=w
theorem fit_r (w:ℕ) (x:Coef) : Width w (fit (tally w,x)) :=
  ⟨t_len ..,t_len ..⟩
@[fun_prop]
theorem disp_easy : Easy disp := by unfold disp; fun_prop
@[fun_prop]
theorem spell_easy : Easy spell := by unfold spell; fun_prop
@[fun_prop]
theorem rest_easy : Easy rest := by unfold rest; fun_prop
@[fun_prop]
theorem fit_easy : Easy fit := by unfold fit; fun_prop
theorem pullG (x:Grain k) : content (disp (Dusk.mark x))=aspect x :=
  QuadraticAlgebra.ext (lifted x.re) (lifted x.im)
theorem pullW (x: Grain k) : Width (k+1) (disp (Dusk.mark x)) :=
  ⟨pull_len _,pull_len _⟩
theorem spellG (x:Coef) (h : Width (k+1) x) :
    spell x=Dusk.mark (wrapMap k (content x)) := Prod.ext (towards _ h.1) (towards _ h.2)
theorem rest_r (n) (x:Coef) : content (rest (tally n,x))=divA n (content x) :=
  QuadraticAlgebra.ext (divpow_v n x.1) (divpow_v n x.2)
theorem fit_small (n) (x:Coef) (h:focus n (content x)) :
    content (fit (tally n,x))=content x := by
  have H {s:S} (i:|whole s| < (2:ℤ)^n) : (whole s).natAbs< (2:ℕ)^n := by
    rw [← Int.natCast_natAbs] at i
    exact_mod_cast i
  apply QuadraticAlgebra.ext <;> unfold fit content
  · exact t_small n _ (H h.1)
  exact t_small n _ (H h.2)

-- common phase multiplication: factors passed carrying sigma; result wrapped
abbrev Orb := Tally×Dusk.Pair
def adjust (x : Dusk.Pair × Orb) : Dusk.Pair :=
  let w := ruler x.1.1
  spell (fit (w,rest (x.2.1,timesG (disp x.1,disp x.2.2))))
@[fun_prop] theorem adjust_p : Charming adjust := by
  have w : Charming (fun x:Dusk.Pair×Orb=> ruler x.1.1) := smooth (by fun_prop)
  have p := smooth spell_easy; have h := smooth fit_easy; have e := smooth rest_easy
  have a := smooth disp_easy; unfold adjust; fun_prop
def split_ (x : Tally × Grain k × Grain k) : Coef :=
  rest (x.1,timesG (disp (Dusk.mark x.2.1),disp (Dusk.mark x.2.2)))
def launch (v : Grain k × Orb) : Grain k :=
  wrapMap k (content (fit (tally (k+1),rest (v.2.1,timesG (disp (Dusk.mark v.1),disp v.2.2)))))
theorem inject (v : Grain k) (p : Orb) :
    adjust (Dusk.mark v,p)=Dusk.mark (launch (v,p)) := by
  have d : ruler (Dusk.mark v).1=tally (k+1) := by simp [ruler,tally,Dusk.mark]
  unfold adjust; dsimp only; rw [d,spellG _ (fit_r _ _)]
  rfl
theorem faithful (n) (v u: Grain k)
    (h : focus k (divA n (aspect v*aspect u))) :
    aspect (launch (v,tally n,Dusk.mark u))=divA n (aspect v*aspect u) := by
  have i := ((rest_r n (timesG (disp (Dusk.mark v),disp (Dusk.mark u)))).trans
    (by rw [key_M,pullG,pullG]))
  let p := rest (tally n,timesG (disp (Dusk.mark v),disp (Dusk.mark u)))
  change content p= _ at i
  have v' : focus (k+1) (content p) := by
    rw [i,focus,tiny,pow_succ]
    have y := pow_pos (show 0<(2:ℤ) by decide) k
    unfold focus tiny at h
    norm_num1 at *
    exact ⟨lt_of_lt_of_le h.1 (by omega),lt_of_lt_of_le h.2 (by omega)⟩
  change aspect (wrapMap k (content (fit (tally _,p))))=_
  rw [fit_small _ _ v',i,recovers _ h]
theorem ferry {I:Type} (k:I→ℕ) (f:I→ Orb) (x:(i:I)→Grain (k i))
    (C:ℕ) (h : ∀ i,size (f i) ≤ C*(k i+1)) :
    Carries (cost k)
      (fun i=> send (Dusk.mark (x i),f i))
      (fun i=> send (Dusk.mark (launch (x i,f i)))) := by
  have D : ∃ K:ℕ,∀ i,size (Dusk.mark (x i),f i) ≤ K*(k i+1) := by
    refine ⟨8+C,fun i=>?_⟩
    rw [size_prod,Dusk.volume]; specialize h i; nlinarith
  obtain ⟨j,d⟩ := D
  have t := (Grid.Charming.slide _ adjust_p j d).bill
  simpa only [Function.comp_def,inject] using t

end Grid

end IntegerMultiplication
end Computability
end OAI
