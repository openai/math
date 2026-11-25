import OAI.Computability.NearSquareRoot.InterchangeBank
import OAI.Computability.NearSquareRoot.InterchangeStageScript

/-!
# Interpreting a finite interchange script by charged tape programs

The renderer describes the physical bank at the boundary of each instruction.
The address space may depend on the input, and instruction lists and register
sets are fixed. A vector of symbols is realized as a fixed collection of
separate scalar rows, charging a reroute once for each copied physical row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress
  NearSquareRoot.Interchange.StageScript

variable {I Y X₀ M E A B : Type} {X : I → Type} {job : Job Y} {r : Regime I}
  {N l : I → ℕ} {zone : I → Y → Prop} {π : (i : I) → M → Equiv.Perm (X i)}
  {price : M → ℕ} {copies : ℕ}

/-- Semantics and charged P192 interface for the two instructions. `copies` is
the number of scalar stream reroutes implementing one semantic move. -/
structure Compiler (r : Regime I) (N l : I → ℕ) (job : Job Y) (zone : I → Y → Prop)
    (E : Type) (π : (i : I) → M → Equiv.Perm (X i)) (price : M → ℕ) (copies : ℕ) where
  render {A : Type} : Series A → ((i : I) → A → X i → E) → I → Tree
  positive : ∀ i, 1 ≤ N i
  alive {A : Type} (rows : Series A) (x : (i : I) → A → X i → E) :
    Alive r N l (render rows x)
  pointwise {A B : Type} [Fintype A] [Fintype B] (rows : Series A) (out : Series B)
      (x : (i : I) → A → X i → E) (τ : (A → E) → B → E) :
    Drive r N l (render rows x) (render out (fun i b u => τ (fun a => x i a u) b))
  route {A B : Type} [Fintype A] [Fintype B] (rows : Series A) (out : Series B)
      (x : (i : I) → A → X i → E) (sel : B → A) (moves : B → M) :
    Hopto job r N l zone (↑(copies * ∑ b, price (moves b)) : ℤ)
      (together r.header (render rows x))
      (render out (fun i b u => x i (sel b) ((π i (moves b)).symm u)))

namespace Compiler

private noncomputable def finiteSeries (A : Type) [Fintype A] : Series A :=
  ⟨Finset.univ.toList, Finset.nodup_toList _, fun a => by simp⟩

private noncomputable def endOrder : {A B : Type} → Program M E A B → Series B
  | _, B, @Program.table _ _ _ _ _ fb _ => @finiteSeries B fb
  | _, B, @Program.route _ _ _ _ _ fb _ _ => @finiteSeries B fb
  | _, _, .seq _ q => endOrder q

/-- Interpret the entire script with one charged request list. The logarithmic
header work is measured in the `mass` bound of the resulting `Hopto`. -/
theorem run (machine : Compiler r N l job zone E π price copies) (program : Program M E A B)
    (rows : Series A) (out : Series B) (x : (i : I) → A → X i → E) :
    Hopto job r N l zone (↑(copies * cost price program) : ℤ)
      (together r.header (machine.render rows x))
      (machine.render out (fun i => eval (π i) program (x i))) := by
  induction program with
  | table τ =>
    rw [cost_table, Nat.mul_zero, Nat.cast_zero]
    exact Hopto.tarry (machine.pointwise rows out x τ)
  | route sel moves => exact machine.route rows out x sel moves
  | seq before after ih₁ ih₂ =>
    let mid := endOrder before
    let middle i := eval (π i) before (x i)
    have h := sequence machine.positive (machine.alive rows x) (machine.alive mid middle)
      (ih₁ rows mid x) (ih₂ mid out middle)
    simpa only [cost_seq, eval_seq, middle, Nat.mul_add, Nat.cast_add] using h

/-- Realize a row of vector values on separate physical streams. A table may
mix all lanes and all source registers at the common address. -/
def lanes {R : Type} [Fintype R] (lane : Series R)
    (base : Compiler r N l job zone E π price copies) :
    Compiler r N l job zone (R → E) π price (copies * Fintype.card R) where
  render rows x := base.render (lane.cart rows) (fun i ra u => x i ra.2 u ra.1)
  positive := base.positive
  alive rows x := base.alive (lane.cart rows) (fun i ra u => x i ra.2 u ra.1)
  pointwise rows out x τ :=
    base.pointwise (lane.cart rows) (lane.cart out) (fun i ra u => x i ra.2 u ra.1)
      (fun v rb => τ (fun a j => v (j,a)) rb.2 rb.1)
  route rows out x sel moves := by
    have h := base.route (lane.cart rows) (lane.cart out) (fun i ra u => x i ra.2 u ra.1)
      (fun rb => (rb.1, sel rb.2)) (fun rb => moves rb.2)
    simpa only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.mul_assoc] using h

end Compiler

/-- One per-symbol move certificate suffices to execute arbitrary banks and
their compositions. This also works with a strengthened child request zone. -/
def symbolCompiler [Finite E] (points : (i : I) → Series (X i)) (st : Station r points)
    (sym : E → Tree) (hs : Function.Injective sym)
    (move : ∀ (μ : M) (v : (i : I) → X i → E),
      Hopto job r (fun i => (points i).count) l zone (price μ)
        (together r.header (stackRun points (fun i => sym ∘ v i)))
        (stackRun points (fun i => sym ∘ v i ∘ (π i μ).symm))) :
    Compiler r (fun i => (points i).count) l job zone E π price 1 where
  render rows x := bank points rows sym x
  positive := st.1
  alive rows x := bank_alive points st rows sym x
  pointwise rows out x τ := table points st rows out sym sym hs x τ
  route rows out x sel moves := by
    let s i a := stripe (points i) (sym ∘ x i a)
    let t i b := stripe (points i) (sym ∘ x i (sel b) ∘ (π i (moves b)).symm)
    have h := collect st.1 rows out s t sel (price ∘ moves)
      (fun a => (finite_manifest (l:=l) sym (fun i => x i a)).lives st)
      (fun b => (finite_manifest (l:=l) sym (fun i => x i (sel b) ∘ (π i (moves b)).symm)).lives st)
      (fun b => move (moves b) (fun i => x i (sel b)))
    rw [Nat.one_mul, Nat.cast_sum]
    exact h

end InterchangeBank

end NearSquareRoot
end Computability
end OAI
