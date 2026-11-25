import OAI.Computability.IntegerMultiplication.Cap.Harmony

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cap
open Finset IntegerMultiplication.Fourier Nat
variable {d:ℕ} {s:Bounds d} [∀ i,NeZero (s i)] (q: Fin d→ℕ)
noncomputable def pulse (x y: Along s) (t:Vector_ s):ℂ :=
  sing s (fun i=> -(q i:ℤ))
    (fun z=> sing s (fun i=>(q i:ℤ)) x z*sing s (fun i=>(q i:ℤ)) y z) t /(space s:ℂ)
variable (h:Nice s)
noncomputable def caster : Fin (space s) ≃ Vector_ s :=
  (rank s).symm.trans (tune h)
-- make noncomp
omit [∀ (i : Fin d), NeZero (s i)] in
theorem figure (x:Fin (space s)) : tune h ((rank s).symm x)= caster h x := rfl

omit [∀ (i : Fin d), NeZero (s i)] in
theorem figureSum (x y z:Fin (space s)) :
    (∀ i,(caster h x i).val+(caster h y i).val≡(caster h z i).val [MOD s i]) ↔
      x.val+y.val≡ z.val [MOD space s] := by
  have e v : amount s ((rank s).symm v) = v.val :=
    congrArg Fin.val ((rank s).apply_symm_apply v)
  rw [← e x, ← e y, ← e z, ← turn_sum h]
  rfl

-- switch coordinates
noncomputable def reboot (x : Fin (space s) → ℂ) : Along s :=
  x ∘ (caster h).symm
noncomputable def combine (x y:Fin (space s)→ℂ) (t:Fin (space s)) : ℂ :=
  ∑ u:Fin (space s),∑ v:Fin (space s),
    if u.val+v.val≡t.val [MOD space s] then x u*y v else 0
theorem engine (p:∀ i,Nat.Coprime (s i) (q i)) (x y) (t:Fin (space s)):
    pulse q (reboot h x) (reboot h y) (caster h t)=combine x y t := by
  classical
  unfold pulse combine
  rw [Cap.renders s q p]
  rw [← (caster h).sum_comp (fun a=>∑ b:Vector_ s, _)]
  refine sum_congr rfl (fun i _=> ?_)
  -- inner
  have E (x:Vector_ s→ℂ):(∑ b:Fin (space s),x (caster h b))=∑ b,x b:=(caster h).sum_comp x
  change ∑ b:Vector_ s,_=_
  rw [← E _]
  refine sum_congr rfl fun j _=> ?_
  simp only [show ((∀ v,((caster h) i v).val+((caster h) j v).val ≡ ((caster h) t v).val [MOD s v])=
    (i.val+j.val≡t.val [MOD space s])) from propext (figureSum h ..)] -- rewrites proof
  -- dependent
  unfold reboot; simp

/-- date index coefficients from approximant. -/
def tally (x y:Fin (space s)→ ℕ) (t:Fin (space s)) : ℕ :=
  ∑ u:Fin (space s),∑ v:Fin (space s), if u.val+v.val=t.val then x u*y v else 0
variable {M n:ℕ}
omit [∀ (i : Fin d), NeZero (s i)] in
theorem tally_complex (x y:Fin (space s)→ℕ) (r:Fin (space s)) (K:ℕ)
    (hx:∀ v,K≤v.val → x v=0) (hy:∀ v,K≤v.val → y v=0) (q0:2*K≤ space s) :
    combine (s:=s) (fun i=>(x i:ℂ)) (fun i=>(y i:ℂ)) r = (tally (s:=s) x y r:ℂ) := by
  unfold combine tally
  push_cast
  refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_
  -- simp only
  rcases lt_or_ge i.val K with t|t
  · rcases lt_or_ge j.val K with u|u
    · have p:i.val+j.val<space s:=by omega
      simp only [Nat.ModEq,Nat.mod_eq_of_lt p,Nat.mod_eq_of_lt r.isLt]
    · rw [hy _ u]
      aesop
  rw [hx _ t]
  aesop

theorem engineN (p:∀ i,Nat.Coprime (s i) (q i)) (x y:Fin (space s)→ℕ) (r:Fin (space s)) (K:ℕ)
    (hx:∀ v,K≤v.val → x v=0) (hy:∀ v,K≤v.val → y v=0) (q0:2*K≤ space s) :
    pulse q (reboot h (fun i=>(x i:ℂ))) (reboot h (fun i=>(y i:ℂ))) (caster h r)= (tally (s:=s) x y r:ℂ) := by
  rw [engine q h p,tally_complex x y r K hx hy q0]

/-- evaluation by radix in the naturals. -/
def score (t:ℕ) (x:Fin M→ℕ) : ℕ := ∑ i:Fin M, t^i.val*x i
omit [∀ (i : Fin d), NeZero (s i)] in
theorem scoreboard (t) (x y : Fin (space s)→ℕ) (K:ℕ)
    (hx:∀ v,K≤v.val → x v=0) (hy:∀ v,K≤v.val → y v=0) (q0:2*K≤ space s) :
    score t (tally (s:=s) x y)=score t x * score t y := by
  unfold score tally
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  rw [sum_comm]
  apply sum_congr rfl; intro j _
  rcases lt_or_ge i.val K with p|p
  · rcases lt_or_ge j.val K with c|c
    · have h : i.val+j.val < space s := by omega
      let k : Fin (space s):= ⟨_,h⟩
      rw [sum_eq_single k]
      · rw [ite_eq_left rfl]
        change t^(i.val+j.val)*_=_
        rw [pow_add]; ring
      · intro u _ e
        have hh : i.val+j.val≠u.val:=fun m=>e (Fin.ext m.symm)
        simp [hh]
      · simp
    simp [hy j c]
  simp [hx i p]

-- coarse bound K capacity and each entry.
omit [∀ (i : Fin d), NeZero (s i)] in
theorem tally_bound (t) (x y:Fin (space s)→ℕ)
    (h:∀ i,x i<t) (p:∀ i,y i<t) (r):
    tally (s:=s) x y r ≤ (space s)^2*t^2 := by
  unfold tally
  calc
   _ ≤ ∑ _i:Fin (space s),∑ _j:Fin (space s), t*t := by
    apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    split
    · gcongr; exact (h i).le; exact (p j).le
    exact Nat.zero_le _
   _ = _ := by simp; ring

end Cap

end IntegerMultiplication
end Computability
end OAI
