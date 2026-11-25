import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudget
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetClock
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchSemantics
import OAI.Computability.NearSquareRoot.CRTControlledBoundedSchedule
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Releasing a batched permutation layer

The physical loop takes the same chronological list of forward/backward switch stages
as the packed Beneš semantics. A single bound on pass workspace applies to every prefix,
while the clock pays for all pass descriptors and the final output copy. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open Filter IntegerMultiplication Code Space Benes

/-- The typed stage list consumed by the bounded schedule interpreter. -/
def order (k d : ℕ) := batchOrder (width k) (batches d k)

theorem order_count {k d : ℕ} (hd : d ≤ k) (room : 8*width k ≤ k) :
    (order k d).length ≤ 32*140^2*(1+Nat.clog 2 (k+1))^2 := by
  simpa only [order,batchOrder_length,passes,Controlled.stageSchedule_length] using pass_count hd room

abbrev Stage := (Bool × ℕ) × ℕ

/-- Polynomially sized microstage descriptors fit together in the array arena.
Only descriptors occurring in the chronological schedule need a size bound. -/
theorem eventually_order_forest (C h : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ (d : ℕ) (key : Stage → Tree), d ≤ k → 8*width k ≤ k →
      (∀ a ∈ order k d, (key a).count ≤ C*(1+k)^h) →
      (Task.forest key (order k d)).count ≤ 2^k := by
  let G : ℕ := 32*140^2
  filter_upwards [eventually_polynomial_le_array_length ((G*(C+1)+1:ℕ):ℝ)
    (by positivity) (h+2)] with k hk
  intro d key hd room bound
  let n := (order k d).length
  let b := 1+k
  have top : (G*(C+1)+1)*b^(h+2) ≤ 2^k := by exact_mod_cast hk
  have log : Nat.clog 2 (k+1) ≤ k := Nat.clog_le_of_le_pow
    (show k+1 ≤ 2^k from Nat.lt_pow_self (by decide : 1 < 2))
  have count : n ≤ G*b^2 := (order_count hd room).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_left log 1) _))
  have csum := costSum_le bound
  have constant : ∀ l : List Stage, costSum (fun _ => C*b^h) l = l.length*(C*b^h) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih, Nat.add_mul, Nat.add_comm]
  rw [constant] at csum
  have power (q : ℕ) : 1 ≤ b^q := Nat.one_le_pow _ _ (by dsimp [b]; omega)
  have header : 1+C*b^h ≤ (C+1)*b^h := by
    rw [Nat.add_mul, Nat.one_mul]
    have := power h
    omega
  rw [Task.forest_count]
  calc
    _ ≤ n*(1+C*b^h)+1 := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right (Nat.add_le_add_left csum n) 1
    _ ≤ (G*b^2)*((C+1)*b^h)+b^(h+2) := Nat.add_le_add (Nat.mul_le_mul count header) (power _)
    _ = (G*(C+1)+1)*b^(h+2) := by rw [pow_add]; ring
    _ ≤ _ := top

/-- Run all the stages, reusing the per-stage arena, and identify the result
as the scatter by the represented block permutations on arbitrary record data. -/
theorem bounded_order {X E R : Type*} (k d : X → ℕ)
    (w : (x : X) → Fin (d x) → ℕ) (tbl : (x : X) → E → Fin (d x) → RawTable)
    (p : (x : X) → E → (i : Fin (d x)) → Equiv.Perm (Word (w x i)))
    (ht : ∀ x e b, RawRepresents (p x e b) (tbl x e b))
    (hw : ∀ x b, w x b ≤ width (k x)) (room : ∀ x, 8*width (k x) ≤ k x)
    (key : X → Stage → Tree) (box : (x : X) → (PackedAddress E (w x) → R) → Tree)
    (charge : X → Stage → ℕ) (allowance volume : X → ℕ)
    (step : BoundedTask
      (fun i : (x : X) × {a // a ∈ order (k x) (d x)} × (PackedAddress E (w x) → R) =>
        charge i.1 i.2.1)
      (fun i => volume i.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (Benes.scatter (batchStage (fun b => b.val / capacity (k i.1))
        (w i.1) (tbl i.1) i.2.1.val.1 i.2.1.val.2) i.2.2)))
    (forestCap : ∀ x, (Task.forest (key x) (order (k x) (d x))).count ≤ volume x)
    (dataCap : ∀ x a, (box x a).count ≤ volume x)
    (callCap : ∀ x, ∀ a ∈ order (k x) (d x), charge x a + (key x a).count + 1 ≤ allowance x) :
    BoundedTask
      (fun i : (x:X) × (PackedAddress E (w x) → R) => (order (k i.1) (d i.1)).length * allowance i.1 + 1)
      (fun i => volume i.1)
      (fun i => .fork (Task.forest (key i.1) (order (k i.1) (d i.1))) (box i.1 i.2))
      (fun i => box i.1 (Benes.scatter (controlledPerm (p i.1)) i.2)) := by
  let next (x : X) (v : PackedAddress E (w x) → R) (a : Stage) :=
    Benes.scatter (batchStage (fun b => b.val / capacity (k x)) (w x) (tbl x) a.1 a.2) v
  have run := Controlled.boundedSchedule (fun x => order (k x) (d x)) key box next
    charge allowance volume step forestCap dataCap callCap
  apply run.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro i
  exact congrArg (box i.1) (batchData_run _ _ _ (p i.1) (ht i.1) (width (k i.1))
    (batches (d i.1) (k i.1)) (hw i.1) (fun b => batch_index_lt (capacity_pos (room i.1)) b) i.2)

/-- Rounded target clock for the permutation, measured on its actual array volume. -/
noncomputable def layerClock (α : ℝ) (k V : ℕ) : ℕ := ⌈(V:ℝ)*(1+(k:ℝ))^α⌉₊

theorem eventually_order_charge (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (h deg : ℕ)
    {ρ α : ℝ} (hρ : 0 ≤ ρ) (hρα : ρ < α) :
    ∀ᶠ k : ℕ in atTop, ∀ (d V allowance : ℕ), d ≤ k → 8*width k ≤ k → 2^k ≤ V →
      (allowance:ℝ) ≤ C*V*(1+(k:ℝ))^ρ*(1+Real.log (2+(k:ℝ)))^h + P*(1+(k:ℝ))^deg →
      (order k d).length * allowance ≤ 2*layerClock α k V := by
  filter_upwards [eventually_layer_clock (32*140^2) C P hC hP h deg hρ hρα] with k hk
  intro d V allowance hd room cap ha
  have cover := hk V (order k d).length cap (order_count hd room)
  have clock : (V:ℝ)*(1+(k:ℝ))^α ≤ (layerClock α k V:ℝ) := Nat.le_ceil _
  have budget := (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α := ℝ) (order k d).length)).trans cover
  exact_mod_cast budget.trans (show 2*(V:ℝ)*(1+(k:ℝ))^α ≤ 2*(layerClock α k V:ℝ) by linarith only [clock])

/-- A single threshold suffices for every family of bounded stage implementations.
The released machine pays the output copy and retains a constant times the arena
as its bound on distinct tape cells. -/
theorem release_order {X : Type*} (k d V allowance : X → ℕ) (input output : X → Tree)
    (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (h deg : ℕ) {ρ α : ℝ} (hρ : 0 ≤ ρ) (hρα : ρ < α) :
    ∃ K : ℕ, (∀ x, K ≤ k x) → (∀ x, d x ≤ k x) → (∀ x, 8*width (k x) ≤ k x) →
      (∀ x, 2^(k x) ≤ V x) →
      (∀ x, (allowance x:ℝ) ≤ C*V x*(1+(k x:ℝ))^ρ*(1+Real.log (2+(k x:ℝ)))^h +
        P*(1+(k x:ℝ))^deg) →
      BoundedTask (fun x => (order (k x) (d x)).length * allowance x + 1) V input output →
      BoundedTask (fun x => layerClock α (k x) (V x)) V input output ∧
      ∃ F : ℕ, PhysicalWalsh.TapeRun (fun x => F*layerClock α (k x) (V x)) (fun x => F*V x) input output := by
  obtain ⟨K,large⟩ := eventually_atTop.mp (eventually_order_charge C P hC hP h deg hρ hρα)
  refine ⟨K, fun hk hd room cap rate task => ?_⟩
  have bounded : BoundedTask (fun x => layerClock α (k x) (V x)) V input output :=
    task.bound 2 1 (fun x => by
      have := large _ (hk x) _ _ _ (hd x) (room x) (cap x) (rate x)
      omega) (by simp)
  have dom (x : X) : V x ≤ layerClock α (k x) (V x) := by
    have growth := Real.one_le_rpow (show 1 ≤ 1+(k x:ℝ) by simp) (hρ.trans hρα.le)
    have hr : (V x:ℝ) ≤ (layerClock α (k x) (V x):ℝ) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) (V x)) growth).trans (Nat.le_ceil _)
    exact_mod_cast hr
  obtain ⟨F,physical⟩ := bounded.releaseOfSpaceLeTime dom
  refine ⟨bounded,2*F,physical.mono (fun x => ?_) (fun x => ?_)⟩
  · have hv := cap x
    have pos := Nat.two_pow_pos (k x)
    have := dom x
    calc
      _ ≤ F*(2*layerClock α (k x) (V x)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  · have hv := cap x
    have pos := Nat.two_pow_pos (k x)
    calc
      _ ≤ F*(2*V x) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
