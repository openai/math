import OAI.Computability.MultitapeWeakETH.IntegralResidues
import OAI.Computability.MultitapeWeakETH.WitnessWalkSpace
import OAI.Computability.IntegerMultiplication.Code.Loop
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Finite sums and products of bounded integral-basis representatives -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code Bits Grid
open private literal whole_literal wordAt_ofFn from OAI.Computability.MultitapeWeakETH.IntegralInstructions
open private size_list_le from OAI.Computability.MultitapeWeakETH.WitnessWalkSpace
open scoped Classical
noncomputable section

abbrev Rep := List S
variable {R : Type} [CommRing R] {m : ℕ} (basis : Module.Basis (Fin m) ℤ R)

abbrev modulus (R : Type) [CommRing R] (w : ℕ) := Ideal.span ({(2:R)^w} : Set R)
abbrev Mod (R : Type) [CommRing R] (w : ℕ) := R ⧸ modulus R w

def residue (w : ℕ) (a : Rep) : Mod R w := Ideal.Quotient.mk _ (decodeCoordinates basis a)

def constant (x : R) : Rep := List.ofFn fun i : Fin m => literal (basis.repr x i)

theorem constant_eq (x : R) : decodeCoordinates basis (constant basis x) = x := by
  simpa only [decodeCoordinates,constant,wordAt_ofFn,whole_literal] using basis.sum_repr x

theorem FitsWidth.size_le {w : ℕ} {ws : Rep} (fit : FitsWidth m w ws) : size ws ≤ (2*w+4)*m+1 := by
  have bound := size_list_le ws (2*w+3) (fun a mem => by
    simp only [size_prod,size_word,fit.2 _ mem]
    have b : size a.1 = 1 := by cases a.1 <;> rfl
    omega)
  rw [fit.1] at bound
  exact bound

private abbrev FoldState := Tally × Rep
private abbrev Combine := Tally × (Rep × Rep) → Rep

private def foldStep (op : Combine) (x : FoldState × Rep) : FoldState :=
  (x.1.1,op (x.1.1,x.1.2,x.2))

private theorem fold_poly (op : Combine) (cost : Poly op) (fits : ∀ w a b, FitsWidth m w (op (tally w,a,b))) :
    Poly (fun q : List Rep × FoldState => q.1.foldl (fun s x => foldStep op (s,x)) q.2) := by
  have step : Poly (foldStep op) :=
    (Easy.fst.compose Easy.fst).poly.pair ((show Poly (fun x : FoldState × Rep => (x.1.1,x.1.2,x.2)) by fun_prop).compose cost)
  have bound (xs : List Rep) (start : FoldState) :
      let out := xs.foldl (fun s x => foldStep op (s,x)) start
      out.1 = start.1 ∧ (out.2 = start.2 ∨ FitsWidth m start.1.length out.2) := by
    induction xs generalizing start with
    | nil => exact ⟨rfl,Or.inl rfl⟩
    | cons x xs ih =>
      obtain ⟨eqn,old | done⟩ := ih (foldStep op (start,x))
      · exact ⟨eqn,Or.inr (old ▸ (by simpa only [foldStep,recover_tally] using fits start.1.length start.2 x))⟩
      · exact ⟨eqn,Or.inr done⟩
  apply Poly.fold_left step (8*m+8) 1
  intro q xs _
  let out := xs.foldl (fun s x => foldStep op (s,x)) q.2
  have pair := size_prod out
  have hx := size_tally q.2.1
  obtain ⟨eqn,old | small⟩ := bound xs q.2
  · change size out ≤ _
    change out.1 = _ at eqn
    change out.2 = _ at old
    rw [pair,eqn,old]
    simp only [size_prod,pow_one]
    nlinarith
  · change size out ≤ _
    change out.1 = _ at eqn
    have s : size out.2 ≤ _ := small.size_le
    rw [pair,eqn]
    simp only [size_prod,pow_one]
    nlinarith

def foldRep (op : Combine) (q : (Tally × Rep) × List Rep) : Rep :=
  q.2.foldl (fun a x => op (q.1.1,a,x)) q.1.2

private theorem fold_step_eq (op : Combine) (ls : List Rep) (w : Tally) (a : Rep) :
    ls.foldl (fun s x => foldStep op (s,x)) (w,a) = (w,ls.foldl (fun s x => op (w,s,x)) a) := by
  induction ls generalizing a with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem foldRep_poly (op : Combine) (cost : Poly op) (fits : ∀ w a b, FitsWidth m w (op (tally w,a,b))) :
    Poly (foldRep op) := by
  convert (Easy.exchange.poly.compose (fold_poly op cost fits)).sndCompose using 1
  funext q
  exact (congrArg Prod.snd (fold_step_eq op q.2 q.1.1 q.1.2)).symm

structure ResidueOps (basis : Module.Basis (Fin m) ℤ R) where
  add : Combine
  mul : Combine
  add_cost : Poly add
  mul_cost : Poly mul
  add_fit : ∀ w a b, FitsWidth m w (add (tally w,a,b))
  mul_fit : ∀ w a b, FitsWidth m w (mul (tally w,a,b))
  add_eq : ∀ w a b, residue basis w (add (tally w,a,b)) = residue basis w a + residue basis w b
  mul_eq : ∀ w a b, residue basis w (mul (tally w,a,b)) = residue basis w a * residue basis w b

theorem residue_ops : Nonempty (ResidueOps basis) := by
  obtain ⟨add,mul,ha,hm,ok⟩ := residue_programs basis
  refine ⟨⟨add,mul,ha,hm,fun w a b => (ok w a b).1,fun w a b => (ok w a b).2.1,?_,?_⟩⟩
  · intro w a b
    symm
    rw [residue,residue,residue,← map_add,Ideal.Quotient.mk_eq_mk_iff_sub_mem,Ideal.mem_span_singleton]
    exact (ok w a b).2.2.1
  · intro w a b
    symm
    rw [residue,residue,residue,← map_mul,Ideal.Quotient.mk_eq_mk_iff_sub_mem,Ideal.mem_span_singleton]
    exact (ok w a b).2.2.2

variable {basis} (ops : ResidueOps basis)
theorem fold_add (w : ℕ) (xs : List Rep) (a : Rep) :
    residue basis w (foldRep ops.add ((tally w,a),xs)) = residue basis w a + (xs.map (residue basis w)).sum := by
  induction xs generalizing a with
  | nil => simp [foldRep]
  | cons x xs ih =>
    change residue basis w (foldRep ops.add ((tally w,ops.add (tally w,a,x)),xs)) = _
    rw [ih,ops.add_eq,List.map_cons,List.sum_cons,add_assoc]

theorem fold_mul (w : ℕ) (xs : List Rep) (a : Rep) :
    residue basis w (foldRep ops.mul ((tally w,a),xs)) = residue basis w a * (xs.map (residue basis w)).prod := by
  induction xs generalizing a with
  | nil => simp [foldRep]
  | cons x xs ih =>
    change residue basis w (foldRep ops.mul ((tally w,ops.mul (tally w,a,x)),xs)) = _
    rw [ih,ops.mul_eq,List.map_cons,List.prod_cons,mul_assoc]

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
