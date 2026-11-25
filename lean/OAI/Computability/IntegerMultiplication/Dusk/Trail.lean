import OAI.Computability.IntegerMultiplication.Dusk.Moat
import OAI.Computability.IntegerMultiplication.Net.Second

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dusk
open Code Bits Net.Walsh
private theorem noon (k : ℕ) :
    (2 : day k)^(k+1)=1 := by
  rw [show (2:day k)=((2:ℕ):day k) from rfl,← Nat.cast_pow,← period_s k,Nat.cast_add,ZMod.natCast_self,
    Nat.cast_one,zero_add]

def bend (k : ℕ) := (2:day k)^k
theorem bend_r (k : ℕ) : bend k + bend k=1 := by rw [← mul_two,bend, ← pow_succ,noon]

theorem bends (k b : ℕ) (h : b≤k+1) :
    bend k^b = 2^((k+1)-b) := by
  -- 2^b multiply invertibly
  have t : k+1-b+b=k+1 := Nat.sub_add_cancel h
  have z : bend k*2=1 := by rw [mul_two,bend_r]
  calc
    bend k^b = bend k^b * (2:day k)^(k+1) := by rw [noon,mul_one]
    _ = (bend k*2)^b * 2^(k+1-b) := by
      conv_lhs => arg 2; rw [← t,pow_add]
      rw [mul_pow]; ring
    _ = _ := by rw [z,one_pow,one_mul]

def turn (x : Tally × Word) :=
  let y := cutLists x
  y.2++y.1
theorem easy_turn : Easy turn := by
  unfold turn; fun_prop

/-- rotate little-endian words, never need a wrap normalization because
canonical payload excludes all ones. Proof via one normalization nonetheless. -/
def wind (x : Tally × Word) := plan (ruler x.2,turn x)
theorem wind_easy : Easy wind := by
  exact ((Easy.ruler Easy.snd).pair easy_turn).compose planned

theorem windy (w : Tally) {k} (e : w.length≤k+1) (x : day k) :
    wind (w,trip x)=trip (bend k^w.length * x) := by
  let B := w.length
  let L := (trip x).take B
  let H := (trip x).drop B
  have q : L++H=trip x := List.take_append_drop B (trip x)
  have n : L.length=B := by simp [L,B,e]
  have m : H.length=k+1-B := by simp [H]
  have b : turn (w,trip x)=H++L := rfl
  have t : (ruler (trip x)).length=k+1 := by simp
  have h₁ : B+(k+1-B)=k+1 := by change B≤k+1 at e; omega
  have h : (H++L).length=k+1 := by rw [List.length_append,n,m,Nat.add_comm,h₁]
  unfold wind
  rw [plan_lt (k:=k) t]
  · congr
    rw [b,Bits.value_append,m,bends k _ e]
    have d : x=((Bits.value L+2^B*Bits.value H:ℕ):day k) := by
      rw [← n,← Bits.value_append L H] -- length n mismatch
      rw [q,trips,ZMod.natCast_val,ZMod.cast_id]
    rw [d]
    push_cast
    change _ = (2:day k)^((k+1)-B)*(_+_)
    rw [mul_add,← mul_assoc,← pow_add, add_comm _ B, h₁,noon,one_mul,add_comm]
  rw [b]
  have a := Bits.value_lt (H++L)
  rw [h] at a
  have := certain k; have := period_s k
  omega

abbrev Grain k := QuadraticAlgebra (day k) (-1) 0
abbrev Pair := Word × Word
def mark {k} (x : Grain k) : Pair := (trip x.re,trip x.im)

noncomputable def gaunt (k : ℕ) : Quarter (Grain k) where
  i := ⟨0,1⟩
  half := ⟨bend k,0⟩
  ii := by
    ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  two := by
    ext <;> simp [bend_r,QuadraticAlgebra.im_one,QuadraticAlgebra.re_one]

variable (k : ℕ)
def gather (x : Pair × Pair) : Pair :=
  (mug (x.1.1,x.2.1),mug (x.1.2,x.2.2))
def lower (x : Pair) : Pair := (shade x.1,shade x.2)
def lunar (x : Pair) : Pair := (shade x.2,x.1)
def moon (x : Tally × Pair) : Pair := (wind (x.1,x.2.1),wind (x.1,x.2.2))
@[fun_prop] theorem gather_easy : Easy gather := by
  have z := mug_easy
  unfold gather; fun_prop
@[fun_prop] theorem lower_easy : Easy lower := by have z := shade_easy; unfold lower; fun_prop
@[fun_prop] theorem lunar_easy : Easy lunar := by have z := shade_easy; unfold lunar; fun_prop
@[fun_prop] theorem moon_easy : Easy moon := by have z := wind_easy; unfold moon; fun_prop

@[simp] theorem meet (x y : Grain k) : gather (mark x,mark y)=mark (x+y) := Prod.ext (mugged ..) (mugged ..)
@[simp] theorem lowered (x : Grain k) : lower (mark x)=mark (-x) := Prod.ext (shaded ..) (shaded ..)
theorem lunatic (x : Grain k) : lunar (mark x)=mark ((gaunt k).i*x) := by
  unfold lunar mark; rw [shaded]
  congr 1 <;> simp [gaunt]
theorem way (a) : (gaunt k).half^a=(⟨bend k^a,0⟩ : Grain k) := by
  induction a with
  | zero => ext <;> simp [QuadraticAlgebra.im_one,QuadraticAlgebra.re_one]
  | succ a ih =>
    rw [pow_succ, ih]
    ext <;> simp [gaunt,pow_succ]
theorem moonlit (x : Grain k) (w : Tally) (h : w.length≤k+1) :
    moon (w,mark x)=mark ((gaunt k).half^w.length*x) := by
  unfold moon mark; dsimp only; rw [windy w h, windy w h,way]
  congr 1 <;> simp

def half (x : Pair) := moon ([()],x)
@[fun_prop] theorem half_easy : Easy half :=
  ((Easy.const [()]).pair easy_id).compose moon_easy
@[simp] theorem halve (x : Grain k) : half (mark x)=mark ((gaunt k).half*x) := by
  simpa [half] using moonlit k x [()] (by simp)

-- needed sign masks only {-1, +1, i, 0, -i, ±b}
def lunarPhase (j : Clock) : Pair → Pair :=
  if j=0 then id else if j=1 then lunar else if j=2 then lower else lower ∘ lunar
@[fun_prop] theorem phase_easy (j : Clock) : Easy (lunarPhase j) := by
  unfold lunarPhase
  split; exact easy_id
  split; exact lunar_easy
  split; exact lower_easy
  exact lunar_easy.compose lower_easy

theorem phased (j : Clock) (x : Grain k) :
    lunarPhase j (mark x)=mark ((gaunt k).ph j*x) := by
  unfold lunarPhase Quarter.ph
  split; simp
  split; exact lunatic ..
  split; simp
  simp [lunatic]

-- glaze/streak
def join_ (s : Bool) (x : Pair) :=
  let y := lunar x
  half (gather (x,bif s then lower y else y))
@[fun_prop] theorem join_easy (s : Bool) : Easy (join_ s) := by
  unfold join_
  cases s <;> simp only [Bool.cond_true,Bool.cond_false] <;> fun_prop
@[simp] theorem joined (s : Bool) (x : Grain k) :
    join_ s (mark x)=mark ((gaunt k).glaze s*x) := by
  cases s <;> simp [join_,lunatic,Quarter.glaze,mul_add,add_mul,mul_assoc]

theorem shone (s : Bool) (x : Grain k) :
    join_ (!s) (mark x) = mark ((gaunt k).streak s*x) := by
  rw [joined]
  cases s <;> simp [Quarter.glaze,Quarter.streak, sub_eq_add_neg]

end Dusk

end IntegerMultiplication
end Computability
end OAI
