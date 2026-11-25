import OAI.Computability.IntegerMultiplication.Axon.Count

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Axon
open Net Net.Walsh Net.Tensor IntegerMultiplication.Fourier
open Matrix Complex
noncomputable section
abbrev R (k:ℕ) (i:ℤ) := phase (2^k) i
private theorem R_self (k : ℕ) (i:ℤ) :
    R k ((2^k:ℤ)*i)=1 := by
  rw [R,phase_eq_one]; push_cast
  exact dvd_mul_right ..

private theorem down (k : ℕ) (i:ℤ) :
    R (k+1) (2*i)=R k i := by
  unfold R phase
  congr 1
  push_cast; rw [pow_succ]
  field
private theorem oddR (k : ℕ) (v:ℤ) (e:Odd v) :
    R (k+1) (v*(2^k:ℤ))=-1 := by
  suffices q : R (k+1) (2^k:ℤ)=-1 by
    rw [← q, R,R,phase_inj]
    obtain ⟨t,rfl⟩ := e
    push_cast
    rw [pow_succ]
    exact ⟨t,by ring⟩
  unfold R phase cis
  rw [show (((2^k:ℤ):ℝ)/(((2^(k+1):ℕ)):ℝ))*(2*Real.pi)=Real.pi from ?_]
  · exact Complex.exp_pi_mul_I
  push_cast; rw [pow_succ]; field

private theorem vital (k : ℕ) (q:ℤ) (p:Odd q) (a b:B) :
    R (k+1) (q*pin a*pin b*2^k)= Walsh.F a b := by
  rcases bit_value a with ra|ra <;>
    rcases bit_value b with rb|rb <;> subst a <;> subst b
  · change R _ (q*0*0*_) = (if (0:B)*0=1 then -1 else 1)
    simp [R,phase]
  · change R _ (q*0*1*_) = (if (0:B)*1=1 then -1 else 1)
    simp [R,phase]
  · change R _ (q*1*0*_) = (if (1:B)*0=1 then -1 else 1)
    simp [R,phase]
  change R _ (q*1*1*_) = (if (1:B)*1=1 then -1 else 1)
  simp [oddR k q p]
-- local rule
def frequency {k : ℕ} (q : ℤ) (i : Fin k) (x : Face k) :=
  R (k-i.val) (q*pin (x i)*beyond x i)
abbrev Mb (k : ℕ) := Mat (Face k) ℂ
def lineF (k:ℕ) (q : ℤ) : Mb k :=
  Matrix.of (fun x y => R k (q*light x*bold y))

theorem first {k} (x y : Face (k+1)) (q : ℤ) (p:Odd q) :
    lineF (k+1) q x y =
    lineF k q (stem x) (stem y) *
      (frequency q (0:Fin (k+1)) (Loom.join (crest x,stem y)) *
          (Walsh.F (crest x) (crest y):ℂ)) := by
  unfold lineF frequency
  simp only [Matrix.of_apply]
  -- phase exponent
  let a := pin (crest x); let b := pin (crest y)
  let u := light (stem x); let z := bold (stem y)
  rw [born_l x,born y, beyond_b]
  have e := vital k q p (crest x) (crest y)
  rw [← e]
  simp only [show Loom.join (crest x,stem y) 0 = crest x from Loom.first_j _ _,
    show stem (Loom.join (crest x,stem y))=stem y from stem_b ..,Fin.val_zero,Nat.sub_zero]
  push_cast
  change R _ (q*(2*(u:ℤ)+a)*(2^k*(b:ℤ)+z)) = R _ _ * (R _ _ * R _ _)
  calc
   _ = R (k+1) ((2^(k+1):ℤ)*(q*u*b)+(2*(q*u*z)+(q*a*z+q*a*b*2^k))) := by rw [pow_succ]; ring_nf
   _ = _ := by
     unfold R
     simp only [phase_add]
     rw [show phase (2^(k+1):ℕ) _ = 1 from R_self (k+1) (q*u*b)]
     rw [one_mul]; rw [show phase (2^(k+1):ℕ) (2*(q*u*z)) = _ from down k (q*u*z)]
-- symmetry with tails bits
theorem step {k} (x:Face (k+1)) (i:Fin k) (q :ℤ) :
    frequency q i.succ x = frequency q i (stem x) := by
  simp [frequency,beyond_s, Fin.val_succ]
end
end Axon

end IntegerMultiplication
end Computability
end OAI
