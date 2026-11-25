import OAI.Computability.IntegerMultiplication.Cone.Emit

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Echo Scale IntegerMultiplication.Fourier Cap Param
variable {n:ℕ} (h:Season n)
include h
theorem bars :
    Nice (modulus n) := by
  constructor
  · intro i
    have h₀ : 2 ≤ P n := (lane2 n).trans (Nat.le_self_pow (by decide) _)
    exact h₀.trans (h.budget_ i i.isLt)
  intro i j z
  exact axis_separation _ i.isLt j.isLt fun v=>z (Fin.ext v)
theorem ration (i: Direction n) :
    Nat.Coprime (modulus n i) (criterion n i) :=
  ((h.odd i i.isLt).coprime_two_right).pow_right _

abbrev List_ n := Fin (space (modulus n))→ℕ
/-- input coefficients tensor ordered and zero padded -/
noncomputable def edition (q:List_ n) : Land n :=
  shell (reboot (bars h) fun i=>(q i:ℂ))
noncomputable def contents (i:Fin (space (modulus n))):Vector_ (criterion n):=
  patch (pitch h) (caster (bars h) i)

theorem book (x y:List_ n) (a:Fin (space (modulus n)))
    (P:∀ i,Param.amount n ≤ i.val → x i=0) (Q:∀ i,Param.amount n ≤ i.val → y i=0):
    idealPulse n (edition h x) (edition h y) (contents h a) =
      (Cap.tally (s:=modulus n) x y a:ℂ) := by
  -- compose shell
  unfold idealPulse edition contents
  rw [exterior h, exterior h,Echo.shell_pt,exterior h,barter]
  have Z:=engineN (s:=modulus n) (criterion n) (bars h)
    (ration h) x y a (Param.amount n) P Q h.enoughBits
  simpa only [source,Bool.cond_false,div_one,Bool.cond_true,pulse] using Z

theorem chapter {x:List_ n} (p:∀ i,x i ≤ 2^P n):
    Bound (edition h x) (hi n 1) := by
  unfold edition
  apply strip_line
  intro i
  change ‖(x _:ℂ)‖≤_
  rw [Complex.norm_natCast]
  unfold hi
  rw [one_mul]
  exact_mod_cast p _

variable {I:Type} (r:I→ℕ) (z:Faculty r) (t:z.quality r) (i:I) (s:Season (r i))
variable (x:Organ (r i)) (a:Angled (r i) x)
omit h
include t a
theorem rounds (b c:List_ (r i)) (u v:Farm (r i))
    (w : array_ (r i) u=edition s b) (X :array_ (r i) v=edition s c)
    (Y:∀ k,b k≤2^P (r i)) (Z:∀ k,c k≤2^P (r i))
    (U:∀ k,Param.amount (r i) ≤ k.val → b k=0)
    (V:∀ k,Param.amount (r i) ≤ k.val → c k=0)
    (k:Fin (space (modulus (r i)))):
    ‖array_ (r i) (glint r z i s x u v) (contents s k) -
      (Cap.tally (s:=modulus (r i)) b c k:ℂ)‖<1/4 := by
  let n:=r i
  have P:= flash r z t i s x a u v (w.symm ▸ chapter s Y) (X.symm ▸ chapter s Z)
  rw [w,X] at P
  -- rewrites also LHS? w only inputs outside glint
  have e:= P (contents s k)
  rw [book s b c k U V] at e
  exact e.trans_lt (final_eps r i)
end Cone

end IntegerMultiplication
end Computability
end OAI
