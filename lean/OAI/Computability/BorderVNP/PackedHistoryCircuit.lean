import OAI.Computability.BorderVNP.PackedHistoryNode

/-! # An actual bottom-up Boolean circuit over all public shortening rounds

The input consists of the original free wires and a static array of guessed
profile slots. Each subtree is evaluated exactly once. Its output state and
acceptance bit are fed into the existing local frame for the next round.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {n : ℕ} {σ : Type*} [Fintype σ] {k b : ℕ} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]

/-- The per-round physical state transform and local validity bit. -/
abbrev Steps (k b : ℕ) (W G : ℕ → Type) [∀ j, Fintype (W j)] [∀ j, Fintype (G j)] :=
  ∀ n, n < b → Frame (LocalPins k (W n) (G n)) (Result (W (n+1)))

/-- A leaf frame attached to its original inputs with a true validity wire. -/
private noncomputable def leaf (f : Frame σ (W 0)) : Frame (σ ⊕ Slot k G 0) (Result (W 0)) :=
  Crossing.parallelFrame (f.subst (Frame.initial Sum.inl))
    ((Frame.initial (id : σ ⊕ Slot k G 0 → _)).step (fun _ : Unit => .const true))

private def restrict (n : ℕ) (i : Fin k) : σ ⊕ Slot k G n → σ ⊕ Slot k G (n+1) :=
  Sum.elim Sum.inl (fun g => .inr (.inl (i,g)))

/-- A child node reads its own disjoint profile slots. -/
def childGuess (g : Slot k G (n+1) → Bool) (i : Fin k) (j : Slot k G n) : Bool := g (.inl (i,j))

/-- Guesses at the current node are shared inputs to its physical layout transform. -/
def nodeGuess (g : Slot k G (n+1) → Bool) (j : G n) : Bool := g (.inr j)

variable (step : Steps k b W G)

/-- Compile the ordered finite history tree. Only physical nodes contribute gate lists.
Alternative profiles are runtime inputs to the same fragment. -/
noncomputable def compile : (n : ℕ) → n ≤ b → Leaves k (Frame σ (W 0)) n →
    Frame (σ ⊕ Slot k G n) (Result (W n))
  | 0, _, f => leaf f
  | n+1, hn, fs => combine (step n (by omega))
      (fun i => (compile n (by omega) (fs i)).subst (Frame.initial (restrict n i))) (fun g => .inr (.inr g))

/-- Read a compiled subtree's physical output state. -/
noncomputable def output (n : ℕ) (hn : n ≤ b) (fs : Leaves k (Frame σ (W 0)) n)
    (x : σ → Bool) (g : Slot k G n → Bool) (w : W n) :=
  (compile step n hn fs).eval (Sum.elim x g) (.inl w)

/-- Read a compiled subtree's single validity flag. -/
noncomputable def flag (n : ℕ) (hn : n ≤ b) (fs : Leaves k (Frame σ (W 0)) n)
    (x : σ → Bool) (g : Slot k G n → Bool) :=
  (compile step n hn fs).eval (Sum.elim x g) (.inr ())

theorem output_zero (f : Frame σ (W 0)) (x : σ → Bool) (g : Slot k G 0 → Bool) :
    output step 0 (Nat.zero_le b) f x g = f.eval x := by
  have h : (Frame.initial (Sum.inl : σ → σ ⊕ Slot k G 0)).eval (Sum.elim x g) = x := funext fun j => Frame.initial_eval _ _ j
  funext j
  simp [output,compile,leaf,h]

theorem flag_zero (f : Frame σ (W 0)) (x : σ → Bool) (g : Slot k G 0 → Bool) :
    flag step 0 (Nat.zero_le b) f x g = true := by
  simp [flag,compile,leaf,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]

private theorem restrict_eval (n : ℕ) (i : Fin k) (x : σ → Bool) (g : Slot k G (n+1) → Bool) :
    (Frame.initial (restrict n i)).eval (Sum.elim x g) = Sum.elim x (childGuess g i) := by
  funext p
  cases p <;> simp [restrict, childGuess]
  rfl

/-- Live local inputs at a nonleaf, expressed in terms of its already computed child outputs. -/
noncomputable def localInput (n : ℕ) (hn : n+1 ≤ b) (fs : Leaves k (Frame σ (W 0)) (n+1))
    (x : σ → Bool) (g : Slot k G (n+1) → Bool) : LocalPins k (W n) (G n) → Bool :=
  Sum.elim (fun p => output step n (by omega) (fs p.1) x (childGuess g p.1) p.2) (nodeGuess g)

theorem output_succ (n : ℕ) (hn : n+1 ≤ b) (fs : Leaves k (Frame σ (W 0)) (n+1))
    (x : σ → Bool) (g : Slot k G (n+1) → Bool) (w : W (n+1)) :
    output step (n+1) hn fs x g w = (step n hn).eval (localInput step n hn fs x g) (.inl w) := by
  simp only [output,compile,combine_state,Frame.subst_eval,restrict_eval,localInput]
  rfl

theorem flag_succ (n : ℕ) (hn : n+1 ≤ b) (fs : Leaves k (Frame σ (W 0)) (n+1))
    (x : σ → Bool) (g : Slot k G (n+1) → Bool) :
    flag step (n+1) hn fs x g = true ↔
      (∀ i, flag step n (by omega) (fs i) x (childGuess g i) = true) ∧
      (step n hn).eval (localInput step n hn fs x g) (.inr ()) = true := by
  simp only [flag,compile,combine_flag,Frame.subst_eval,restrict_eval,localInput,output]
  rfl

/-- A property holds at every bottom bundle in an ordered tree. -/
def everyLeaf {T : Type*} (test : T → Prop) : (n : ℕ) → Leaves k T n → Prop
  | 0, a => test a
  | n+1, a => ∀ i, everyLeaf test n (a i)

/-- The per-node physical frames and initial bundles give the cost of the full DAG, with
no factor depending on the number of profile assignments. -/
theorem compile_size (n : ℕ) (hn : n ≤ b) (fs : Leaves k (Frame σ (W 0)) n) (L M : ℕ)
    (hl : everyLeaf (fun f : Frame σ (W 0) => f.size ≤ L) n fs)
    (hm : ∀ j (hj : j<n), (step j (lt_of_lt_of_le hj hn)).size + (2*k+4) ≤ M) :
    (compile step n hn fs).size ≤ historyTreeCost k (L+1) M n := by
  induction n with
  | zero =>
    change fs.size ≤ L at hl
    have hc := Frame.step_size_le (Frame.initial (id : σ ⊕ Slot k G 0 → _)) (fun _ : Unit => .const true) 1 (fun _ => le_rfl)
    simp only [Frame.initial_size, Fintype.card_unit, one_mul, zero_add] at hc
    let f : Frame σ (W 0) := fs
    change (leaf (k := k) (G := G) f).size ≤ L+1
    simp only [leaf,Crossing.parallelFrame_size,Frame.subst_size,Frame.initial_size,zero_add]
    exact Nat.add_le_add hl hc
  | succ n ih =>
    let hs (i : Fin k) := (compile step n (by omega) (fs i)).subst (Frame.initial (restrict n i))
    have hchild (i : Fin k) : (hs i).size ≤ historyTreeCost k (L+1) M n := by
      simpa [hs] using ih (by omega) (fs i) (hl i) (fun j hj => hm j (by omega))
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hchild i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hsum
    apply (combine_size (step n hn) hs (fun g => .inr (.inr g))).trans
    simp only [historyTreeCost, Nat.add_assoc]
    exact Nat.add_le_add hsum (hm n (by omega))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
