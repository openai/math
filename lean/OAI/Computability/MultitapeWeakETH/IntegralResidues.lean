import OAI.Computability.MultitapeWeakETH.IntegralInstructions
import Mathlib.Data.Int.ModEq

/-! # Bounded-word evaluation of an integral-basis arithmetic expression -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code Bits Grid
open private wordAt wordAt_poly encodeAll wordAt_ofFn from OAI.Computability.MultitapeWeakETH.IntegralInstructions
open scoped Classical
noncomputable section

private def clip (x : Tally × S) : S := (x.2.1,resize (x.1,x.2.2))

private theorem clip_poly : Poly clip := by
  apply Easy.poly
  unfold clip
  fun_prop

private theorem clip_whole (w : ℕ) (a : S) :
    Int.ModEq ((2:ℤ)^w) (whole (clip (tally w,a))) (whole a) := by
  change Int.ModEq _ (tag a.1 * (value (sized w a.2) : ℤ)) _
  rw [sized_low,Int.natCast_mod,Nat.cast_pow,Nat.cast_ofNat]
  exact (Int.mod_modEq (value a.2) _).mul_left _

private def clipAll {m : ℕ} (x : Tally × List S) :=
  List.ofFn fun j : Fin m => clip (x.1,wordAt j.val x.2)

private theorem clipAll_poly (m : ℕ) : Poly (clipAll (m:=m)) :=
  encodeAll _ fun j => (Easy.fst.poly.pair (Easy.snd.poly.compose (wordAt_poly j.val))).compose clip_poly

/-- The output always occupies m signed coordinates of exactly w magnitude bits. -/
def FitsWidth (m w : ℕ) (ws : List S) := ws.length = m ∧ ∀ a ∈ ws, a.2.length = w

private theorem clipAll_fits (m w : ℕ) (ws : List S) : FitsWidth m w (clipAll (m:=m) (tally w,ws)) := by
  refine ⟨List.length_ofFn,?_⟩
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact sized_length w _

variable {R : Type} [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R)

/-- Reduce all coordinates modulo a common power of two. -/
private theorem clipAll_congr (w : ℕ) (ws : List S) :
    (2:R)^w ∣ decodeCoordinates basis ws - decodeCoordinates basis (clipAll (m:=m) (tally w,ws)) := by
  simp only [decodeCoordinates,clipAll,wordAt_ofFn,← Finset.sum_sub_distrib,← sub_smul]
  apply Finset.dvd_sum
  intro i _
  obtain ⟨c,hc⟩ := (clip_whole w (wordAt i.val ws)).dvd
  refine ⟨c • basis i,?_⟩
  rw [hc,mul_smul,zsmul_eq_mul,Int.cast_pow,Int.cast_ofNat]

/-- Addition and multiplication use polynomial bit time and emit bounded-size
representatives on every call, independently of the number of prior calls. -/
theorem residue_programs :
    ∃ add mul : Tally × (List S × List S) → List S, Poly add ∧ Poly mul ∧
      ∀ w x y, let p := (tally w,x,y)
        FitsWidth m w (add p) ∧ FitsWidth m w (mul p) ∧
        ((2:R)^w ∣ decodeCoordinates basis x + decodeCoordinates basis y - decodeCoordinates basis (add p)) ∧
        ((2:R)^w ∣ decodeCoordinates basis x * decodeCoordinates basis y - decodeCoordinates basis (mul p)) := by
  obtain ⟨a,b,ha,hb,eval⟩ := coordinate_programs basis
  refine ⟨_,_,(Easy.fst.poly.pair (Easy.snd.poly.compose ha)).compose (clipAll_poly m),
    (Easy.fst.poly.pair (Easy.snd.poly.compose hb)).compose (clipAll_poly m),?_⟩
  intro w x y p
  refine ⟨clipAll_fits m w _,clipAll_fits m w _,?_,?_⟩
  · simpa only [(eval x y).1] using clipAll_congr basis w (a (x,y))
  · simpa only [(eval x y).2] using clipAll_congr basis w (b (x,y))

include basis in
/-- A fixed nonzero coordinate of one detects scaled natural counts. The
word length grows linearly with the number of factors and the input bits. -/
theorem scaled_count_residue [Nontrivial R] [CharZero R] (d : ℤ) (hd : d ≠ 0) :
    ∃ A : ℕ, ∀ n M c : ℕ, c ≤ 2^n →
      ((2:R)^(A*(M+1)+n+1) ∣ ((d^M*(c:ℤ) : ℤ) : R) ↔ c = 0) := by
  have someCoord : ∃ i, basis.repr 1 i ≠ 0 := by
    by_contra! hz
    have e : basis.repr 1 = 0 := Finsupp.ext fun i => hz i
    exact one_ne_zero (basis.repr.map_eq_zero_iff.mp e)
  obtain ⟨i,hi⟩ := someCoord
  let a := basis.repr 1 i
  let A := a.natAbs+d.natAbs+1
  refine ⟨A,?_⟩
  intro n M c hc
  constructor
  · rintro ⟨y,hy⟩
    have repr : (d^M*(c:ℤ))*a = (2:ℤ)^(A*(M+1)+n+1) * basis.repr y i := by
      have eq : (d^M*(c:ℤ)) • (1:R) = (2:ℤ)^(A*(M+1)+n+1) • y := by
        simpa only [zsmul_eq_mul,mul_one,Int.cast_pow,Int.cast_ofNat] using hy
      simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul,a] using congrArg (fun x => basis.repr x i) eq
    have hdiv : 2^(A*(M+1)+n+1) ∣ d.natAbs^M*c*a.natAbs := by
      simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,show (2:ℤ).natAbs = 2 by decide] using
        (show ((2:ℤ)^(A*(M+1)+n+1)).natAbs ∣ ((d^M*(c:ℤ))*a).natAbs from
          ⟨(basis.repr y i).natAbs,by rw [repr,Int.natAbs_mul]⟩)
    have ha : a.natAbs ≤ 2^A := by have := Nat.lt_two_pow_self (n:=A); dsimp [A] at *; omega
    have dd : d.natAbs ≤ 2^A := by have := Nat.lt_two_pow_self (n:=A); dsimp [A] at *; omega
    have size : d.natAbs^M*c*a.natAbs ≤ 2^(A*(M+1)+n) := by
      calc
        _ ≤ (2^A)^M*2^n*2^A := by gcongr
        _ = _ := by rw [← pow_mul,← pow_add,← pow_add]; congr 1; ring
    by_contra ne
    have ah : a ≠ 0 := hi
    have positive : 0 < d.natAbs^M*c*a.natAbs := by positivity
    have := Nat.le_of_dvd positive hdiv
    rw [pow_succ] at this
    have := Nat.two_pow_pos (A*(M+1)+n)
    omega
  · rintro rfl
    simp

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
