import OAI.Hierarchy.DescentWalshPhysical
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

namespace OAI
/-! # Signed intermediate bounds and modular output of the physical Walsh transform -/

namespace Hierarchy.DescentWalshPhysical
open scoped Fin.CommRing
variable {m b : ℕ}

theorem layer_abs (t : Fin m) (x : Cube m→ℤ) (B : ℤ) (bound : ∀p,|x p|≤B) (p : Cube m) :
    |layer t x p|≤2*B := by
  have u := abs_le.mp (bound (Function.update p t false))
  have v := abs_le.mp (bound (Function.update p t true))
  unfold layer
  split <;> apply abs_le.mpr <;> constructor <;> omega

theorem steps_abs (ts : List (Fin m)) (x : Cube m→ℤ) (B : ℤ)
    (bound : ∀p,|x p|≤B) (p : Cube m) : |steps ts x p|≤2^ts.length*B := by
  induction ts generalizing x B with
  | nil => simpa [steps] using bound p
  | cons t ts ih =>
    have h := ih (layer t x) (2*B) (layer_abs t x B bound)
    simpa only [steps,List.foldl_cons,List.length_cons,pow_succ,mul_assoc] using h

theorem transform_abs (x : Cube m→ℤ) (B : ℤ) (bound : ∀p,|x p|≤B) (p : Cube m) :
    |transform x p|≤2^m*B := by
  simpa only [transform,List.length_reverse,List.length_finRange] using
    steps_abs (List.finRange m).reverse x B bound p

theorem numerator_partial_abs (ts : List (Fin m)) (x : Cube m→ℤ) (B : ℤ)
    (bound : ∀p,|x p|≤B) (p : Cube m) :
    |steps ts (fun a=>transform x a*transform x a) p|≤2^(ts.length+2*m)*B^2 := by
  have square (a : Cube m) : |transform x a*transform x a|≤(2^m*B)^2 := by
    rw [abs_mul,pow_two]
    exact mul_self_le_mul_self (abs_nonneg _) (transform_abs x B bound a)
  have iter := steps_abs ts (fun a=>transform x a*transform x a) ((2^m*B)^2) square p
  apply iter.trans_eq
  rw [pow_add,Nat.two_mul,pow_add]
  ring

theorem numerator_abs (x : Cube m→ℤ) (B : ℤ) (bound : ∀p,|x p|≤B) (p : Cube m) :
    |numerator x p|≤2^(3*m)*B^2 := by
  simpa only [numerator,transform,List.length_reverse,List.length_finRange,
    show m+2*m=3*m by omega] using numerator_partial_abs (List.finRange m).reverse x B bound p

theorem layer_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (t : Fin m) (x : Cube m→R) : layer t (fun a=>f (x a))=fun a=>f (layer t x a) := by
  funext p
  by_cases bit : p t=true <;> simp [layer,bit]

theorem steps_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (ts : List (Fin m)) (x : Cube m→R) : steps ts (fun a=>f (x a))=fun a=>f (steps ts x a) := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    change steps ts (layer t (fun a=>f (x a)))=fun a=>f (steps ts (layer t x) a)
    rw [layer_map f]
    exact ih _

theorem transform_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (x : Cube m→R) : transform (fun a=>f (x a))=fun a=>f (transform x a) :=
  steps_map f _ _

theorem numerator_map {R S : Type*} [Ring R] [Ring S] (f : R→+*S)
    (x : Cube m→R) : numerator (fun a=>f (x a))=fun a=>f (numerator x a) := by
  unfold numerator
  rw [transform_map f]
  simp only [←map_mul]
  exact transform_map f _

theorem steps_cast (b : ℕ) (ts : List (Fin m)) (x : Cube m→ℤ) (p : Cube m) :
    steps ts (fun a=>(x a:Fin (2^b))) p=((steps ts x p : ℤ) : Fin (2^b)) :=
  congrFun (steps_map (Int.castRingHom (Fin (2^b))) ts x) p

theorem numerator_cast (b : ℕ) (x : Cube m→ℤ) (p : Cube m) :
    numerator (fun a=>(x a:Fin (2^b))) p=((numerator x p : ℤ) : Fin (2^b)) :=
  congrFun (numerator_map (Int.castRingHom (Fin (2^b))) x) p

/-- The preceding signed values only need to be represented modulo the word
width. A true natural final coefficient that fits can be read without a sign bit. -/
theorem numerator_val (b : ℕ) (x : Cube m→ℕ) (p : Cube m) (v : ℕ)
    (exactValue : numerator (fun a=>(x a:ℤ)) p=(v:ℤ)) (fits : v<2^b) :
    (numerator (fun a=>(x a:Fin (2^b))) p).val=v := by
  have s := numerator_cast b (fun a=>(x a:ℤ)) p
  rw [exactValue] at s
  have word : numerator (fun a=>(x a:Fin (2^b))) p=(v:Fin (2^b)) := by simpa using s
  rw [word,Fin.val_cast_of_lt fits]

theorem nonnegative_val (b : ℕ) (x : Cube m→ℤ) (p : Cube m) (live : 0≤numerator x p)
    (fits : (numerator x p).toNat<2^b) : (numerator (fun a=>(x a:Fin (2^b))) p).val=(numerator x p).toNat := by
  rw [numerator_cast]
  conv_lhs => rw [←Int.toNat_of_nonneg live,Int.cast_natCast]
  exact Fin.val_cast_of_lt fits

/-- Actual old natural input rows yield their measured autocorrelation. -/
theorem correlation_word (b : ℕ) (x : Cube m→ℕ) (d : Cube m) (M : ℕ)
    (bound : ∀a,x a≤M) (room : 2^(3*m)*M^2<2^b) :
    (numerator (fun a=>(x a:Fin (2^b))) d).val =
      2^m * ∑a : Cube m,x a*x (fun i=>(a i).xor (d i)) := by
  let v := 2^m * ∑a : Cube m,x a*x (fun i=>(a i).xor (d i))
  have eval : numerator (fun a=>(x a:ℤ)) d=(v:ℤ) := by
    rw [numerator_exact]
    simp only [v,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sum]
  have limit := numerator_abs (fun a=>(x a:ℤ)) (M:ℤ) (by
    intro a
    simpa only [Nat.abs_cast] using (Int.ofNat_le.mpr (bound a))) d
  rw [eval,abs_of_nonneg (Int.natCast_nonneg v)] at limit
  exact numerator_val b x d v eval ((show v≤2^(3*m)*M^2 by exact_mod_cast limit).trans_lt room)

theorem correlation_bound (x : Cube m→ℕ) (d : Cube m) (M : ℕ) (bound : ∀a,x a≤M) :
    2^m*(∑a : Cube m,x a*x (fun i=>(a i).xor (d i)))≤2^(2*m)*M^2 := by
  have each := Finset.sum_le_sum (s:=Finset.univ) (fun (a : Cube m) _=>
    Nat.mul_le_mul (bound a) (bound (fun i=>(a i).xor (d i))))
  have size : Fintype.card (Cube m)=2^m := by simp [Cube]
  calc
    _ ≤ 2^m*(∑_ : Cube m,M*M) := Nat.mul_le_mul_left _ each
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,size,nsmul_eq_mul,Nat.cast_id,Nat.two_mul,pow_add,pow_two];ring

/-- Reading the finished transform only needs the sharper bound from the true
autocorrelation, even when intermediate signed magnitudes exceed a word. -/
theorem correlation_word_sharp (b : ℕ) (x : Cube m→ℕ) (d : Cube m) (M : ℕ)
    (bound : ∀a,x a≤M) (room : 2^(2*m)*M^2<2^b) :
    (numerator (fun a=>(x a:Fin (2^b))) d).val =
      2^m * ∑a : Cube m,x a*x (fun i=>(a i).xor (d i)) := by
  apply numerator_val b x d
  · rw [numerator_exact]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sum]
  · exact (correlation_bound x d M bound).trans_lt room

end Hierarchy.DescentWalshPhysical

end OAI
