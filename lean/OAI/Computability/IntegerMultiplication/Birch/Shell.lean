import OAI.Computability.IntegerMultiplication.Cone.Banner

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Birch
open Grid Bits Code Carry Cone
-- disk-round to nonnegative integer, natural bounds delivered with approximation powers
variable (w n:ℕ)
private theorem rounded (x:ℕ)
    (p: |(x:ℝ)/(2:ℝ)^(w+1)-n| ≤ 1/2-1/4):
    (x+2^w)/2^(w+1) = n := by
  have h : (0:ℕ)<2^w := by positivity
  rw [abs_le] at p
  have h0 : (0:ℝ)<2^w := by positivity
  rw [pow_succ] at *
  have y: (n:ℝ) -1/4 ≤ x/((2:ℝ)^w*2) := by linarith [p.1]
  have z: (x:ℝ)/((2:ℝ)^w*2) ≤ n+1/4 := by linarith [p.2]
  rw [le_div_iff₀ (by positivity)] at y
  rw [div_le_iff₀ (by positivity)] at z
  have A : n*(2^w*2) ≤ x+2^w := by
    exact_mod_cast (show (n:ℝ)*(2^w*2) ≤ (x:ℝ)+2^w by nlinarith)
  have B : x+2^w < (n+1)*(2^w*2) := by
    exact_mod_cast (show (x:ℝ)+2^w< (n+1)*(2^w*2) by nlinarith)
  exact Nat.le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr B))
    ((Nat.le_div_iff_mul_le (by omega)).mpr A)
private theorem empty (x:ℕ)
    (p: |-(x:ℝ)/(2:ℝ)^(w+1)-n| < 1/2):
    n=0 := by
  rw [abs_lt] at p
  have e : 0 ≤ (x:ℝ)/ (2:ℝ)^(w+1) := by positivity
  by_contra h
  have f : (1:ℝ)≤ n := by exact_mod_cast Nat.pos_of_ne_zero h
  rw [neg_div] at p; linarith

def breath (x:Tally × S) :=
  let y:=x.2
  let q:= Carry.flash x.1
  let z := Bits.add (y.2,q)
  bif y.1 then ([]:Word) else
    (cutLists (()::x.1,z)).2

@[fun_prop] theorem easyB : Easy breath := by
  unfold breath; dsimp only
  apply Carry.condition
  · fun_prop
  · fun_prop
  have z := Carry.easy_flash
  exact (easy_cut ((show Easy (fun x:Tally×S=> (()::x.1,Bits.add (x.2.2,Carry.flash x.1))) from by fun_prop))).sndCompose

private theorem shift_ (w) (x:Word):
    value (x.drop w)=value x /2^w := by
  induction w generalizing x with
  | zero=>simp
  | succ w ih=>cases x with
    | nil=>simp
    | cons b x=>
      change value (x.drop w)=_
      simp only [pow_succ',← Nat.div_div_eq_div_mul,value_half,ih]

theorem listen (x:S)
    (p: |(Grid.whole x:ℝ)/(2:ℝ)^(w+1)-n|≤1/4):
    value (breath (tally w,x))=n := by
  rcases x with ⟨b,x⟩
  unfold breath; dsimp only
  cases b
  · simp only [Bool.cond_false,cutLists]
    simp only [List.length_cons,tally_length]
    rw [shift_, add_val,Carry.flash_v,tally_length]
    apply rounded
    have p0 : (Grid.whole ((false:Bool),x):ℝ)=(value x:ℝ) := by simp [tag,whole]
    rw [p0] at p
    linarith
  rw [Bool.cond_true,value_nil, empty w n (value x)]
  simp only [whole,tag] at p
  push_cast at p
  simp only [Bool.cond_true,Int.cast_neg,Int.cast_one,neg_one_mul] at p
  linarith

theorem listen_length (x:S) :
    List.length (breath (tally w,x)) ≤ dept x+w+2 := by
  unfold breath; cases h:x.1
  all_goals
    change (bif x.1 then ([]:Word) else _).length ≤ _
    simp [h,cutLists,Carry.flash,fill,tally_length,Bits.add_length,dept]
  all_goals omega

def roundedG (x:Tally × Dusk.Pair) : Word :=
  breath (x.1,(Grid.disp x.2).1)
@[fun_prop] theorem fluent : Easy roundedG := by unfold roundedG; fun_prop
variable {k:ℕ}
theorem rests (x:Dusk.Grain k)
    (h: ‖meaning (w+1) k x-(n:ℂ)‖≤(1:ℝ)/4):
    value (roundedG (tally w,Dusk.mark x))=n := by
  apply listen
  have a:= (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re, Complex.natCast_re] at a
  have Q : ((meaning (w+1) k x)).re = ((aspect x).re:ℝ)/(2:ℝ)^(w+1) := by
    unfold meaning
    rw [show (2:ℂ)^(w+1)=↑((2:ℝ)^(w+1)) by push_cast; rfl,Complex.div_ofReal]
    simp [Grid.toC]
  rw [Q,← Grid.pullG] at a
  exact a
theorem range_ (x:Dusk.Grain k):
    List.length (roundedG (tally w,Dusk.mark x)) ≤ k+1+w+2 := by
  apply (listen_length w ((Grid.disp (Dusk.mark x)).1)).trans
  rw [(Grid.pullW x).1]
end Birch

end IntegerMultiplication
end Computability
end OAI
