import OAI.Computability.IntegerMultiplication.Brief.Blot
import OAI.Computability.IntegerMultiplication.Grid.Faith

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Strip Staff Carry Grid Complex
variable {J:Type} (r:Regime J)
def Curve (f:J→ℂ) := Blot r (fun i=> (f i).re) ∧ Blot r (fun i=> (f i).im)
namespace Curve
variable {r}
theorem real {f:J→ℝ} (h : Blot r f) :
    Curve r (fun i=>(f i:ℂ)) := ⟨h,by simpa [Blot,Curve] using (Blot.constant (r:=r) (0:ℤ))⟩
theorem imag {f:J→ℝ} (h : Blot r f):
    Curve r (fun i=> (f i:ℂ)*Complex.I) := by
  unfold Curve; simp; exact ⟨(by simpa using (Blot.constant (r:=r) (0:ℤ))),h⟩
theorem constant (n:ℤ) :
    Curve r (fun _=>(n:ℂ)) := by simpa only [Complex.ofReal_intCast] using Curve.real (Blot.constant (r:=r) n)
variable {x y:J→ℂ} (h:Curve r x) (p:Curve r y)
include h p
theorem add : Curve r (fun i=>x i+y i) :=
  ⟨h.1.adding p.1,h.2.adding p.2⟩
theorem sub : Curve r (fun i=>x i-y i) :=
  ⟨h.1.sub p.1,h.2.sub p.2⟩
theorem mul : Curve r (fun i=>x i *y i) :=
  ⟨(h.1.times p.1).sub (h.2.times p.2),
    (h.1.times p.2).adding (h.2.times p.1)⟩
omit p
theorem fixedPower (k:ℕ) : Curve r (fun i=>x i^k) := by
  induction k with
  | zero=> simp only [pow_zero]; simpa using (constant (r:=r) 1)
  | succ n ih=> simp_rw [pow_succ]; exact ih.mul h

-- Complex I power alternating ±
omit h in
theorem oddity {n:J→ℕ} (v:Realizes r n) :
    Curve r (fun i=>Complex.I^n i) := by
  let H:Blot r (fun _=>(-1:ℝ)) := by simpa only [Int.cast_neg,Int.cast_one] using (Blot.constant (r:=r) (-1))
  have u: Blot r (fun i=>(-1:ℝ)^(n i/2)) := H.power (v.dividing (.fix 2))
  have w: Classified r (fun i=> n i%2=0) := by
    have T:= (Realizes.below (Realizes.rem v (.fix 2)) (.fix 1))
    simpa only [Nat.lt_one_iff] using T
  have i₁:= real u
  have i₂:= imag u
  unfold Curve
  have t (i): Complex.I^(n i)=(if n i%2=0 then ((-1)^(n i/2):ℂ)
    else ((-1)^(n i/2):ℂ)*Complex.I) := by
    have eq : 2*(n i/2) + n i%2=n i:= by omega
    nth_rw 1 [← eq]
    rw [pow_add,pow_mul,I_sq]
    split
    · next h=>rw [h,pow_zero,mul_one]
    · next h=>rw [show n i%2=1 by omega,pow_one]
  simp_rw [t,show ∀ j:ℕ,(-1:ℂ)^j= ((↑((-1:ℝ)^j)):ℂ) by simp]
  have T₁ : Curve r (fun i=> if n i%2=0 then (↑((-1:ℝ)^(n i/2)):ℂ) else ↑((-1:ℝ)^(n i/2))*Complex.I) := by
    unfold Curve; simp only [apply_ite Complex.re, apply_ite Complex.im]
    exact ⟨i₁.1.choice i₂.1 w,i₁.2.choice i₂.2 w⟩
  exact T₁

omit h
theorem sums {n:J→ℕ} {v:Realizes r n} (f:(i:J)→Fin (n i)→ℂ)
    (h:Curve (signal n v) (fun i:Across n=> f i.1 i.2)) :
    Curve r (fun i=>∑ j:Fin (n i),f i j) := by
  unfold Curve
  simp only [Complex.re_sum,Complex.im_sum]
  exact ⟨Blot.sums _ _ _ h.1, Blot.sums _ _ _ h.2⟩
end Curve
end Brief

end IntegerMultiplication
end Computability
end OAI
