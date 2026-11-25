import OAI.Computability.IntegerMultiplication.Brief.Mantissa
import OAI.Computability.MultitapeWeakETH.IntegralSums

/-! # Polynomial-time signed-word programs for arithmetic in a fixed integral basis -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code Bits Grid
open scoped Classical
noncomputable section

private def literal (z : ℤ) : S := (decide (z<0),phrase (z.natAbs+1) z.natAbs)

private theorem whole_literal (z : ℤ) : whole (literal z) = z := by
  have h : z.natAbs < 2^(z.natAbs+1) := by have := Nat.lt_two_pow_self (n:=z.natAbs+1); omega
  simp only [literal,whole,value_phrase h,Int.natCast_natAbs,tag]
  by_cases e : z < 0
  · simp [e,abs_of_neg e]
  · simp [e,abs_of_nonneg (le_of_not_gt e)]

private def wordAt : ℕ → List S → S
  | 0, ws => List.casesOn ws (literal 0) (fun x _ => x)
  | i+1, ws => wordAt i (List.casesOn ws [] (fun _ tail => tail))

private theorem wordAt_poly (i : ℕ) : Poly (wordAt i) := by
  induction i with
  | zero => exact (Easy.listCase (literal 0) (Easy.fst (X:=S) (Y:=List S))).poly
  | succ i ih =>
    have tail : Easy (fun ws : List S => List.casesOn (motive := fun _ => List S) ws [] (fun _ t => t)) := Easy.listCase [] Easy.snd
    exact tail.poly.compose ih

private theorem wordAt_ofFn {m : ℕ} (w : Fin m → S) (i : Fin m) : wordAt i.val (List.ofFn w) = w i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ]
    refine Fin.cases rfl (fun j => ?_) i
    exact ih _ j

/-- The native tree codec carries a finite list of signed binary words.
A fixed basis determines the number and order of coordinates. -/
def decodeCoordinates {R : Type} [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R) (ws : List S) : R :=
  ∑ i : Fin m, whole (wordAt i.val ws) • basis i

private def SignedPoly {X : Type} [Codec X] (v : X → ℤ) :=
  ∃ w : X → S, Poly w ∧ ∀ x, whole (w x) = v x

private theorem fixedInt {X : Type} [Codec X] (z : ℤ) : SignedPoly (fun _ : X => z) :=
  ⟨fun _ => literal z,Code.Poly.const _,fun _ => whole_literal _⟩

private theorem plusInt {X : Type} [Codec X] {a b : X → ℤ}
    (left : SignedPoly a) (right : SignedPoly b) : SignedPoly (fun x => a x+b x) := by
  obtain ⟨f,hf,ef⟩ := left
  obtain ⟨g,hg,eg⟩ := right
  exact ⟨_,(hf.pair hg).compose easy_plus.poly,fun x => (plus_v _ _).trans (by rw [ef,eg])⟩

private theorem timesInt {X : Type} [Codec X] {a b : X → ℤ}
    (left : SignedPoly a) (right : SignedPoly b) : SignedPoly (fun x => a x*b x) := by
  obtain ⟨f,hf,ef⟩ := left
  obtain ⟨g,hg,eg⟩ := right
  exact ⟨_,(hf.pair hg).compose Brief.timeP,fun x => (Brief.timeV _ _).trans (by rw [ef,eg])⟩

private theorem sumInt {X J : Type} [Codec X] (s : Finset J) (a : J → X → ℤ)
    (each : ∀ j, SignedPoly (a j)) : SignedPoly (fun x => ∑ j ∈ s, a j x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (fixedInt (X:=X) 0)
  | insert j s hj ih => simpa only [Finset.sum_insert hj] using plusInt (each j) ih

private theorem encodeAll {X : Type} [Codec X] {m : ℕ} (f : Fin m → X → S) (h : ∀ i, Poly (f i)) :
    Poly (fun x => List.ofFn (fun i => f i x)) := by
  induction m with
  | zero => simpa using (Code.Poly.const (X:=X) ([] : List S))
  | succ m ih =>
    simp only [List.ofFn_succ]
    exact ((h 0).pair (ih (fun i => f i.succ) (fun i => h i.succ))).compose Poly.cons

private theorem pack {X R : Type} [Codec X] [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R)
    (v : X → R) (each : ∀ i, SignedPoly (fun x => basis.repr (v x) i)) :
    ∃ f : X → List S, Poly f ∧ ∀ x, decodeCoordinates basis (f x) = v x := by
  choose w hw eq using each
  refine ⟨_,encodeAll w hw,fun x => ?_⟩
  simpa only [decodeCoordinates,wordAt_ofFn,eq] using basis.sum_repr (v x)

private theorem unpack {X R : Type} [Codec X] [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R)
    (g : X → List S) (hg : Poly g) (i : Fin m) :
    SignedPoly (fun x => basis.repr (decodeCoordinates basis (g x)) i) := by
  refine ⟨_,hg.compose (wordAt_poly i.val),fun x => ?_⟩
  exact (congrFun (basis.repr_sum_self (fun j => whole (wordAt j.val (g x)))) i).symm

/-- Both operations are fixed finite stack programs with polynomial bit time
on the signed-word input lists, for any fixed integer basis. -/
theorem coordinate_programs {R : Type} [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R) :
    ∃ add mul : List S × List S → List S, Poly add ∧ Poly mul ∧ ∀ x y,
      decodeCoordinates basis (add (x,y)) = decodeCoordinates basis x + decodeCoordinates basis y ∧
      decodeCoordinates basis (mul (x,y)) = decodeCoordinates basis x * decodeCoordinates basis y := by
  let D := decodeCoordinates basis
  have left := unpack basis Prod.fst (Easy.fst (X:=List S) (Y:=List S)).poly
  have right := unpack basis Prod.snd (Easy.snd (X:=List S) (Y:=List S)).poly
  obtain ⟨add,ha,ea⟩ := pack basis (fun p : List S × List S => D p.1 + D p.2) (fun i => by
    simpa [D] using plusInt (left i) (right i))
  have formula (x y : R) (l : Fin m) :
      basis.repr (x*y) l = ∑ i, ∑ j, basis.repr x i * basis.repr y j * basis.repr (basis i*basis j) l := by
    conv_lhs => rw [← basis.sum_repr x,← basis.sum_repr y]
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_smul_comm,map_sum,map_smul,
      Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
  obtain ⟨mul,hm,em⟩ := pack basis (fun p : List S × List S => D p.1 * D p.2) (fun l => by
    rw [show (fun p : List S × List S => basis.repr (D p.1 * D p.2) l) = _ from
      funext fun p => formula (D p.1) (D p.2) l]
    exact sumInt _ _ fun i => sumInt _ _ fun j =>
      timesInt (timesInt (left i) (right j)) (fixedInt (basis.repr (basis i*basis j) l)))
  exact ⟨add,mul,ha,hm,fun x y => ⟨ea (x,y),em (x,y)⟩⟩

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
