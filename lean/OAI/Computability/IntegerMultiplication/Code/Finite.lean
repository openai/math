import OAI.Computability.IntegerMultiplication.Code.Product
import Mathlib.Data.Fintype.Order
import Mathlib.Basic.Finite.Sum

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Constant internal state and finite tables. `parse` is for bounded-depth input and consumes
exactly that value; its continuation, a finite branch tree in the program, can then
operate on any still delimited data.
-/

namespace Code

def parse : ℕ → ℕ → (Tree → Cmd) → Cmd
  | 0, _, _ => .pass
  | n+1,i,c => splitRoot i (fun b => c (.atom b))
    <| parse n i (fun x => parse n i (fun y => c (.fork x y)))

theorem fits_parse (n) (x : Tree) (c : Tree → Cmd) (i : ℕ) (env r r' t)
    (h : Fits env (c x) r r' t) (e : x.count ≤ n) :
    Fits env (parse n i c) (pile i x r) r' (t+4*x.count) := by
  induction x generalizing n c r' r t with
  | atom b =>
    cases n with
    | zero => have h := Tree.count_pos (.atom b); omega
    | succ _ => simpa only [parse,Tree.count] using (fits_bit (c := fun b => c (.atom b)) h)
  | fork x y hx hy =>
    cases n with
    | zero => have h := Tree.count_pos (.fork x y); omega
    | succ n =>
      rw [Tree.count] at e
      have ha := hx n (fun x' => parse n i (fun y => c (.fork x' y))) (pile i y r) _
        (t+4*y.count) (hy n _ r r' t h (by omega)) (by omega)
      rw [Tree.count]
      exact (fits_pair ha).mono (by omega)

/-- `FiniteState` encodings, used for compiling case-based arbitrary continuations.
More general tape transformations use just Codec. -/
class FiniteState (X : Type*) [Codec X] : Prop where
  finite : Finite X := by infer_instance
  identify : Function.Injective (send (X := X))

attribute [instance] FiniteState.finite
instance : FiniteState Bool where
  identify a b := Tree.atom.inj

instance : FiniteState Unit where
  identify a b _ := Subsingleton.elim a b

variable {X Y Z : Type*} [Codec X] [FiniteState X]

instance [Codec Y] [FiniteState Y] : FiniteState (X × Y) where
  identify a b h := Prod.ext (FiniteState.identify ((Tree.fork.inj h).1))
    (FiniteState.identify ((Tree.fork.inj h).2))

instance [Codec Y] [FiniteState Y] : FiniteState (X ⊕ Y) where
  identify a b h := by
    cases a <;> cases b <;> simp_all [FiniteState.identify.eq_iff]

instance : FiniteState (Option X) where
  identify a b h := by
    cases a <;> cases b <;> simp_all [FiniteState.identify.eq_iff]

-- use Nat.findGcd or Finite.exists_le_const
private theorem uniform (f : X → ℕ) : ∃ n, ∀ x, f x ≤ n :=
  ((Set.finite_range f).bddAbove).imp fun _ hu x => hu (Set.mem_range_self x)

namespace Task

theorem finite_select {W : Type*} (v : W → X)
    {a : W → ℕ} {p q : W → Tree}
    (h : ∀ b : X, Task (fun i : {x : W // v x = b} => a i.val)
      (fun i => p i.val) (fun i => q i.val)) :
    Task a (fun x => .fork (send (v x)) (p x)) q := by
  classical
  choose c C hc using h
  obtain ⟨M,hM⟩ := uniform C
  obtain ⟨K,hK⟩ := uniform (fun x : X => (send x).count)
  cases isEmpty_or_nonempty X with
  | inl h =>
    exact ⟨.pass,0,fun x => (IsEmpty.false (v x)).elim⟩
  | inr ne =>
    refine ⟨splitRoot 0 (fun _ => .pass) <|
      parse K 0 (fun w => c (Function.invFun send w)),
      M+4*K+4, fun x env r => ?_⟩
    have he : Function.invFun send (send (v x)) = v x :=
      Function.leftInverse_invFun FiniteState.identify _
    have hs := hc (v x) ⟨x,rfl⟩ env r
    refine (fits_pair (fits_parse _ _ _ _ _ _ _ _ (by rw [he]; exact hs) (hK _))).mono ?_
    simp only [Nat.add_mul, Nat.mul_add,Nat.mul_one]
    have hm : C (v x)*a x ≤ M*a x := Nat.mul_le_mul_right _ (hM _)
    have e₁ := hM (v x)
    have e₂ := hK (v x)
    beta_reduce at e₂
    omega -- specialize more
end Task

/-- Arbitrary function of finite codec-decodable input. -/
theorem Easy.finite [Codec Y] (f : X → Y) : Easy f := by
  let nil := Tree.atom false
  have h := Task.finite_select (W := X) id (p := fun _ => nil) (q := fun x => send (f x))
    (a := fun _ => 1) (fun x => ?_)
  have hu := (Task.supply nil (send (X := X))).compose (Task.exchange (fun _ => nil) send)
  refine (hu.compose h).bound 3 fun x => ?_
  · change 0+(1+size x)+1+1≤3*(size x+1)
    omega
  · exact (Task.const (send (f x)) (fun (_ : {y : X // id y=x}) => nil)).conform (fun _ => rfl) (fun _ => rfl) (fun y => congrArg (fun i : X => send (f i)) (show x=y.val from y.property.symm))

end Code

end IntegerMultiplication
end Computability
end OAI
