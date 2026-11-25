import OAI.ThreeFlat.Diagonal.PhysicalPlaceFibers
import OAI.ThreeFlat.Diagonal.PhysicalStageProgram

namespace OAI
/-! # Oldest physical operands in a terminal history subtree -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction
open scoped Classical BigOperators
variable {F : Type} [Field F]

private def fiberComp {X Y Z : Type*} (f : X → Y) (g : Y → Z) (v : Z) :
    {x // g (f x)=v} ≃ (Σ y : {y // g y=v}, {x // f x=y.val}) where
  toFun x := ⟨⟨f x,x.property⟩,x,rfl⟩
  invFun y := ⟨y.2.val,(congrArg g y.2.property).trans y.1.property⟩
  left_inv _ := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
    change f x = y at hx
    subst y
    rfl

private theorem card_composite {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → Z) (v : Z)
    (a b : ℕ) (first : ∀ y, Nat.card {x // f x=y}=a) (second : Nat.card {y // g y=v}=b) :
    Nat.card {x // g (f x)=v} = a*b := by
  classical
  rw [Nat.card_congr (fiberComp f g v),Nat.card_sigma]
  simp only [first, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
    ← Nat.card_eq_fintype_card,second,Nat.mul_comm]

private def uniform {S : Shape} (P : Plan F S) (q : ℕ) : Prop :=
  ∀ (h : P.History) (v : (P.finish h).Site), Nat.card {x // P.destination h x = v} = q

/-- Every terminal owner's fiber of original physical sites has this cardinality. -/
def Run.DestinationSize {d l : ℕ} {A : State d l} (r : Run F A) (q : ℕ) : Prop := uniform r.plan q

private theorem uniform_cast {S T : Shape} (e : S=T) (p : Plan F S) (q : ℕ) :
    uniform (e ▸ p : Plan F T) q ↔ uniform p q := by cases e; rfl

private theorem dest_recast {d l l' : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) (q : ℕ) :
    (Program.recast e A r).DestinationSize q ↔ r.DestinationSize q := by cases e; rfl

private theorem fibers_recast {d l D D' L q : ℕ} {A : State d l} (e : D=D')
    (R : Move F A D L) (h : R.FiberSize q) : (Program.recastMove e R).FiberSize q := by cases e; exact h

private theorem dest_step {d l D L q p : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t, Run F (R.next t)) (first : R.FiberSize q)
    (rest : ∀ t, (next t).DestinationSize p) : (Run.step R next).DestinationSize (q*p) := by
  rintro ⟨t,h⟩ v
  let Q : Plan F (R.rules.target t) := (R.target_eq t).symm ▸ (next t).plan
  have tail : uniform Q p := (uniform_cast (R.target_eq t).symm _ p).mpr (rest t)
  exact card_composite (R.rules.owner t) (Q.destination h) v q p (first t) (tail h v)

/-- Product of the actual per-pass child multiplicities. -/
def Program.childrenProduct : {s : ℕ} → Program F s → ℕ
  | _, .done _ => 1
  | _, .shrink s _ _ _ tail => (2^s*2^(2*(2^s)+1))*tail.childrenProduct
  | _, .refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.childrenProduct

theorem Program.run_destinationSize {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) : (P.run rem A).DestinationSize P.childrenProduct := by
  induction P with
  | done s =>
    intro _ v
    have equiv : {x : A.Site // id x=v} ≃ Fin 1 :=
      ⟨fun _ => 0,fun _ => ⟨v,rfl⟩,fun x => Subtype.ext x.property.symm,fun _ => Subsingleton.elim _ _⟩
    exact (Nat.card_congr equiv).trans (Nat.card_fin 1)
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    change (recast e A (.step R _)).DestinationSize ((2^s*2^(2*(2^s)+1))*tail.childrenProduct)
    apply (dest_recast ..).mpr
    apply dest_step R _ (shrinkBinary_fiberSize T s (2^t) _ _ _ B)
    exact fun t => ih (R.next t)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    change (recast e A (.step (recastMove degree R) _)).DestinationSize tail.childrenProduct
    apply (dest_recast ..).mpr
    rw [← Nat.one_mul tail.childrenProduct]
    apply dest_step (recastMove degree R) _ (fibers_recast degree R (refreshBinary_fiberSize T B hm hh sym rows zero conn))
    exact fun _ => ih _

theorem Program.childrenProduct_le {s : ℕ} (P : Program F s) : P.childrenProduct ≤ 2^P.charge := by
  induction P with
  | done => rfl
  | shrink s t T small tail ih =>
    simpa only [childrenProduct,charge,pow_add] using Nat.mul_le_mul (shrink_children_le_charge s) ih
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    exact ih.trans (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left _ _))

end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
