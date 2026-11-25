import OAI.Computability.IntegerMultiplication.Star.Shelf
import OAI.Computability.IntegerMultiplication.Fourier.Truncate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief.Signed
open Code Staff Strip Carry IntegerMultiplication.Fourier
variable {I:Type} {r:Regime I}
theorem modulo {a:I→ℤ} {m:I→ℕ} (p:Signed r a) (q:Figure r m)
    (h:∀ i,0< m i) :
    Figure r (fun i=>(a i%(m i:ℤ)).toNat) := by
  let b:=p.down.modded q
  have P:= Figure.variant ((q.subtracted b).modded q) b (p.ordered (.fixed 0))
  have eq i : (a i%(m i:ℤ)).toNat=
      (if a i<0 then (m i-(a i).natAbs%m i)%m i else (a i).natAbs % m i) := by
    let v:=a i
    let t:=m i
    specialize h i
    change (v %(t:ℤ)).toNat=ite _ _ _
    change (v %(t:ℤ)).toNat=(if v<0 then (t-v.natAbs%t)%t else v.natAbs % t)
    split
    · next z=>
      have e : v = - (v.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_neg z]; simp
      let y:= v.natAbs%t
      have u : y<t := Nat.mod_lt _ h
      have v1 : ((t-y:ℕ):ℤ) ≡ v [ZMOD (t:ℤ)] := by
        rw [Nat.cast_sub u.le]
        have Q : (t:ℤ) ≡ 0 [ZMOD t] := Int.modulus_modEq_zero
        have X : (y:ℤ) ≡ -v [ZMOD (t:ℤ)] := by
          unfold y
          rw [Int.natCast_mod,Int.natCast_natAbs,abs_of_neg z]
          simp [Int.ModEq]
        exact (Q.sub X).trans (by simp)
      have i₁ : (((t-y)%t:ℕ):ℤ)=v%(t:ℤ) := by rw [Int.natCast_mod]; exact v1
      simp only [← i₁,Int.toNat_natCast]; rfl
    · next z =>
      have v1 : ((v.natAbs%t:ℕ):ℤ)=v%(t:ℤ) := by rw [Int.natCast_mod,Int.natCast_natAbs,abs_of_nonneg (by omega)]
      rw [← v1, Int.toNat_natCast]
  simp_rw [eq]
  exact P
theorem pin {n:I→ℕ} {a:I→ℤ} (p:Signed r a) (t:Figure r n)
    [e:∀ i,NeZero (n i)] :
    Figure r (fun i=>(wrap (n i) (a i)).val) := p.modulo t (fun _i=> Nat.pos_of_ne_zero (NeZero.ne _))
end Brief.Signed

namespace Star
open Code Staff Strip Carry IntegerMultiplication.Fourier Brief Dusk Grid
variable {X:Type} {r:Regime X} {s t:X→ ℕ} [∀ i,NeZero (t i)] [∀ i,NeZero (s i)]
variable (k:(i:X)→ Spot (t i))
variable (S:Figure r s) (T:Figure r t)
variable (K:Figure r (fun i=>(k i).val)) (l:X→ℤ) (L:Signed r l)
include S T K
omit [∀ (i : X), NeZero (t i)] [∀ (i : X), NeZero (s i)] in
theorem sampled : Figure r (fun i=>floorSample (s i) (t i) (k i)) :=
  (S.multiplied K).quotients T
include L
omit [∀ (i : X), NeZero (t i)] in
theorem wrapping :
    Figure r (fun i=>(nextSample (s:=s i) (k i) (l i)).val) :=
  ((Signed.up (sampled k S T K)).adding L).pin S

-- windows arbitrary indices. n chosen frac+35+2P where all s,t ≤2^P. require working.
omit L
variable (j:(i:X)→Spot (s i))
variable (J:Figure r (fun i=>(j i).val))
variable (D frac w P : X→ℕ) (d:Realizes r D) (p:Realizes r frac) (W:Realizes r w) (E:Realizes r P)
variable (h:∀ i,D i ≤ 2^(2*(P i))) (e : ∀ i, (2:ℝ)^frac i+2 < 2^w i)
include J d p W E h e
theorem winds :
    ∃ f:(i:X)→ Grain (w i), Satisfactory w r f ∧ ∀ i,
      ‖meaning (frac i) (w i) (f i)-win (D i) (k i) (j i)‖ ≤ 3*drop_ (frac i) := by
  let a i : ℝ := (((t i:ℤ)*rep (j i)-(s i:ℤ)*rep (k i):ℤ):ℝ)/((s i*t i:ℕ):ℝ)
  let n i:=35+2*(P i)+frac i
  let v (i:X):ℂ:= sail (n i) (D i) (a i)
  let A i:= t i*(j i).val; let B i:= s i*(k i).val
  have eq i : a i= ((A i:ℝ) -(B i:ℝ))/((s i:ℝ)*t i):= by
    unfold a A B rep; push_cast; rfl
  have Z i : 0<s i:=Nat.pos_of_ne_zero (NeZero.ne _)
  have X0 i : 0<t i:=Nat.pos_of_ne_zero (NeZero.ne _)
  let C := Blot.natural (T.multiplied J)
  have A0:Blot r a := by
    -- undo orientation
    have V := ((Blot.natural (T.multiplied J)).sub (Blot.natural (S.multiplied K))).ratio
      ((Blot.natural S).times (Blot.natural T)) (fun i=>by
        exact_mod_cast Nat.mul_pos (Z i) (X0 i))
    simpa only [a,rep,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul] using V
  have N : Realizes r n :=
    ((Realizes.fix 35).plus (Realizes.times (.fix 2) E)).plus p
  have R : Curve r v := Curve.real (sailRule a A0 _ N _ d)
  have t₀ i : ‖v i‖ ≤ 1 := by simpa only [v,Complex.norm_real,Real.norm_eq_abs] using sail_bound (n i) (D i) (a i)
  obtain ⟨f,q,H⟩ := stroke _ frac w p W R (fun i=> lt_of_le_of_lt (by
    have e := mul_le_mul_of_nonneg_right (t₀ i) (show 0≤(2:ℝ)^frac i by positivity); linarith) (e i))
  refine ⟨f,q,fun i=>?_⟩
  have ai : |a i| ≤ 1 := by
    rw [eq,abs_div]
    have e (s:ℕ) [NeZero s] : (0:ℝ)<s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
    have Te := mul_pos (e (s i)) (e (t i))
    rw [abs_of_pos Te]
    apply (div_le_one Te).2
    have c : (A i:ℝ) ≤ (s i:ℝ)*t i := by
      unfold A; push_cast
      rw [mul_comm]; gcongr; exact_mod_cast (j i).isLt.le
    have c' : (B i:ℝ) ≤ (s i:ℝ)*t i := by
      unfold B; push_cast; gcongr; exact_mod_cast (k i).isLt.le
    rw [abs_le]
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (A i),Nat.cast_nonneg (α:=ℝ) (B i)]
  have h0 : (4:ℕ)≤n i := by unfold n; omega
  have Q : ‖v i-win (D i) (k i) (j i)‖ ≤ drop_ (frac i) := by
    unfold win v; rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply (sails h0 ai (D i)).trans
    have F : (D i:ℝ) ≤ (2:ℝ)^(2*P i) := by exact_mod_cast h i
    unfold n drop_
    calc
     _ ≤ (2*(2:ℝ)^(2*P i))*(2^34*(1/2)^(35+2*P i+frac i)) := by gcongr
     _ = _ := by
       rw [pow_add,pow_add]
       have v₀: (2:ℝ)^(2*P i)*(1/2)^(2*P i)=1:= by rw [← mul_pow]; simp
       have e : (2*(2:ℝ)^(2*P i))*(2^34*(((1/2)^35*(1/2)^(2*P i))*(1/2)^frac i)) =
         (2*2^34*(1/2)^35)*((2:ℝ)^(2*P i)*(1/2)^(2*P i))*((1/2)^frac i) := by ring
       rw [e,v₀]; norm_num
  have mh:= norm_add_le (meaning (frac i) (w i) (f i)-v i)
    (v i-win (D i) (k i) (j i))
  rw [sub_add_sub_cancel] at mh
  linarith [H i]
end Star

end IntegerMultiplication
end Computability
end OAI
