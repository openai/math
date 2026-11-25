import OAI.Computability.BorderVNP.ParseBatchSortCompare
import OAI.Computability.VPVNP.RAMSortLayers
import OAI.Computability.VPVNP.RAMSortCorrect
import OAI.Computability.VPVNP.RAMSortPerm

/-!
# Batched Boolean sorting of binary parse records

Each of Batcher's addressed layers emits one comparison per record and then
uses its shared output to multiplex every bit of that record. The resulting
ordered Boolean DAG has linear cost in the total number of bits per layer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchSort

open VPVNP VPVNP.VerifierNetwork VPVNP.RAMSort
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Live bits in a padded batch of fixed-width records. -/
abbrev Pins (b w : ℕ) := Fin (2 ^ b) × Fin w

variable {σ : Type*} [Fintype σ] {b w : ℕ}

private theorem step_size {τ ρ : Type*} [Fintype τ] [Fintype ρ]
    (f : Frame σ τ) (es : ρ → Expr τ) :
    (f.step es).size = f.size + ∑ j, (es j).size := by
  simp only [Frame.step, Frame.size, CircuitBatch.Frame.step_gate_count_sum,
    StatementCircuit.Expr.size_rename]
  congr 1
  exact (Fintype.equivFin ρ).symm.sum_comp (fun j => (es j).size)

private def mate (j : ℕ) (hj : j < b) (i : Fin (2 ^ b)) : Fin (2 ^ b) :=
  ⟨partner j i.val, partner_lt i.isLt hj⟩

private def flags (j : ℕ) (hj : j < b) : Pins b w ⊕ Fin (2 ^ b) → Expr (Pins b w)
  | .inl z => .input z
  | .inr i => leExpr (fun k => (i, k)) (fun k => (mate j hj i, k))

private def move (j : ℕ) (hj : j < b) (dir : ℕ → Bool) (i : Pins b w) :
    Expr (Pins b w ⊕ Fin (2 ^ b)) :=
  let p := mate j hj i.1
  let first := if i.1.val < p.val then dir i.1.val else !(dir i.1.val)
  let own : Expr (Pins b w ⊕ Fin (2 ^ b)) := .input (.inl i)
  let other : Expr (Pins b w ⊕ Fin (2 ^ b)) := .input (.inl (p, i.2))
  if first then mux (.input (.inr i.1)) own other else mux (.input (.inr i.1)) other own

/-- One addressed comparator layer. The first expression batch computes the
comparison flags. The second reads them by fanout to route each payload bit. -/
noncomputable def layer (f : Frame σ (Pins b w)) (j : ℕ) (hj : j < b)
    (dir : ℕ → Bool) : Frame σ (Pins b w) := (f.step (flags j hj)).step (move j hj dir)

private theorem flags_size (f : Frame σ (Pins b w)) (j : ℕ) (hj : j < b) :
    (f.step (flags j hj)).size = f.size + 2 ^ b * (16 * w + 1) := by
  rw [step_size, Fintype.sum_sum_type]
  simp only [flags, StatementCircuit.Expr.size, leExpr_size, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  ring

private theorem move_size (j : ℕ) (hj : j < b) (dir : ℕ → Bool) (i : Pins b w) :
    (move j hj dir i).size = 8 := by
  dsimp only [move]
  split <;> split <;> rfl

/-- Exact gate count of a layer in the AND/OR/NOT fragment. -/
theorem layer_size (f : Frame σ (Pins b w)) (j : ℕ) (hj : j < b) (dir : ℕ → Bool) :
    (layer f j hj dir).size = f.size + 2 ^ b * (24 * w + 1) := by
  simp only [layer, step_size (f.step (flags j hj)), flags_size, move_size, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  ring

/-- The live bits decode to the indicated integer array on the padded block. -/
def Represents (f : Frame σ (Pins b w)) (x : σ → Bool) (a : ℕ → ℕ) : Prop :=
  ∀ i : Fin (2 ^ b), value (fun k => f.eval x (i, k)) = a i.val

private theorem layer_row (f : Frame σ (Pins b w)) (j : ℕ) (hj : j < b)
    (dir : ℕ → Bool) (x : σ → Bool) (i : Fin (2 ^ b)) :
    (fun k => (layer f j hj dir).eval x (i, k)) =
      let p := mate j hj i
      let own := fun k => f.eval x (i, k)
      let other := fun k => f.eval x (p, k)
      let up := if i.val < p.val then dir i.val else !(dir i.val)
      if up then (if value own ≤ value other then own else other)
      else (if value own ≤ value other then other else own) := by
  dsimp only
  funext k
  simp only [layer, Frame.step_eval, move, apply_ite]
  split <;> simp [mux_eval, StatementCircuit.Expr.eval, flags, leExpr_eval, Function.comp_def, ite_apply]

/-- Bitwise routing realizes the integer compare-exchange layer at each occupied
and padding slot. -/
theorem represents_layer {f : Frame σ (Pins b w)} {x : σ → Bool} {a : ℕ → ℕ}
    (h : Represents f x a) (j : ℕ) (hj : j < b) (dir : ℕ → Bool) :
    Represents (layer f j hj dir) x (comparatorLayer j dir a) := by
  intro i
  rw [layer_row]
  dsimp only
  have hi' := h i
  have hp' := h (mate j hj i)
  simp only [hi', hp']
  cases hd : dir i.val <;> by_cases hi : i.val < (mate j hj i).val <;>
    by_cases hl : a i.val ≤ a (mate j hj i).val <;>
    simp only [mate] at hi hl hp' ⊢ <;>
    simp [hi, hl, hd, comparatorLayer, lower, upper, min_def, max_def, hi', hp']
  all_goals omega

/-- Compile the decreasing strides of one Batcher merge phase. -/
noncomputable def strides (dir : ℕ → Bool) : (k : ℕ) → k ≤ b →
    Frame σ (Pins b w) → Frame σ (Pins b w)
  | 0, _, f => f
  | k + 1, hk, f => strides dir k (by omega) (layer f k (by omega) dir)

/-- Compile all phases in increasing order of block size. -/
noncomputable def phases : (k : ℕ) → k ≤ b → Frame σ (Pins b w) → Frame σ (Pins b w)
  | 0, _, f => f
  | k + 1, hk, f => strides (phaseDirection (k + 1)) (k + 1) hk (phases k (by omega) f)

private theorem strides_size (dir : ℕ → Bool) (k : ℕ) (hk : k ≤ b) (f : Frame σ (Pins b w)) :
    (strides dir k hk f).size = f.size + k * (2 ^ b * (24 * w + 1)) := by
  induction k generalizing f with
  | zero => simp [strides]
  | succ k ih => rw [strides, ih, layer_size]; ring

private theorem represents_strides (dir : ℕ → Bool) (k : ℕ) (hk : k ≤ b)
    {f : Frame σ (Pins b w)} {x : σ → Bool} {a : ℕ → ℕ} (h : Represents f x a) :
    Represents (strides dir k hk f) x (runStrides k dir a) := by
  induction k generalizing f a with
  | zero => exact h
  | succ k ih => exact ih _ (represents_layer h k (by omega) dir)

private theorem represents_phases (k : ℕ) (hk : k ≤ b) {f : Frame σ (Pins b w)}
    {x : σ → Bool} {a : ℕ → ℕ} (h : Represents f x a) :
    Represents (phases k hk f) x (runPhases k a) := by
  induction k with
  | zero => exact h
  | succ k ih => exact represents_strides _ _ hk (ih (by omega))

/-- A sort uses at most a quadratic number of addressed layers. -/
theorem phases_size (k : ℕ) (hk : k ≤ b) (f : Frame σ (Pins b w)) :
    (phases k hk f).size ≤ f.size + k ^ 2 * (2 ^ b * (24 * w + 1)) := by
  induction k with
  | zero => simp [phases]
  | succ k ih =>
    rw [phases, strides_size]
    have hh := ih (by omega)
    calc
      _ ≤ (f.size + k ^ 2 * (2 ^ b * (24 * w + 1))) + (k + 1) * (2 ^ b * (24 * w + 1)) :=
        Nat.add_le_add_right hh _
      _ ≤ _ := by rw [Nat.add_assoc, ← Nat.add_mul]; gcongr; nlinarith

/-- The outputs of the Boolean DAG are the records of the ascending Batcher sort.
The earlier gates of an incoming frame remain shared by all outputs. -/
theorem phases_correct (f : Frame σ (Pins b w)) (x : σ → Bool) :
    (fun i : Fin (2 ^ b) => value (fun k => (phases b le_rfl f).eval x (i, k))) =
      sort b true (fun i => value (fun k => f.eval x (i, k))) := by
  let a (j : ℕ) := if h : j < 2 ^ b then value (fun k => f.eval x (⟨j,h⟩, k)) else 0
  have ha : Represents f x a := fun i => by simp [a, i.isLt]
  have he := represents_phases b le_rfl ha
  have hs := block_runPhases b 0 a
  simp only [Nat.zero_mod, decide_true] at hs
  have hab : block b 0 a = fun i => value (fun k => f.eval x (i, k)) := by
    funext i
    simp [block, a, i.isLt]
  rw [hab] at hs
  funext i
  exact (he i).trans (by simpa [block, a, i.isLt] using congrFun hs i)

end ParseBatchSort

end BorderVNP
end Computability
end OAI
