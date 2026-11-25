import OAI.ThreeFlat.Diagonal.HistoryAssembly

namespace OAI
/-! # Path work of physically emitting every intermediate trivalent record

A postorder copy emits four words for each child row. An original record
can be copied only at its successive ancestors. Empty subtrees still have
a charged node for command setup, even when they contain no trivalent rows.
-/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open scoped BigOperators

variable {F : Type*} {p : ℕ}

def nodes : {p : ℕ} → Tree F p → ℕ
  | _, .atom _ => 1
  | _, .join _ _ _ _ child => 1 + ∑ i, nodes (child i)

def commands : {p : ℕ} → Tree F p → ℕ
  | _, .atom _ => 0
  | _, .join _ _ _ _ child => ∑ i, (commands (child i) + 1)

def copiedRows : {p : ℕ} → Tree F p → ℕ
  | _, .atom _ => 0
  | _, .join _ _ _ _ child => ∑ i, (copiedRows (child i) + (child i).rows)

/-- A terminal history of depth `k` can create a different actual subtree at
each site, many of which end early. -/
inductive Within : ℕ → {p : ℕ} → Tree F p → Prop where
  | atom {p : ℕ} (k : ℕ) (N : BitNetwork F p) : Within k (.atom N)
  | join {p k h c : ℕ} {arity : Fin c → ℕ} {wire : ∀ i, Fin (arity i) → BitSource h p}
      {child : ∀ i, Tree F (arity i)} (hs : ∀ i, Within k (child i)) :
      Within (k+1) (.join h c arity wire child)

theorem command_count (T : Tree F p) : T.commands+1 = T.nodes := by
  induction T with
  | atom N => rfl
  | join h c arity wire child ih => simp only [commands,nodes,ih,Nat.add_comm]

theorem rowCopies_le {k : ℕ} {T : Tree F p} (H : Within k T) : T.copiedRows ≤ k*T.rows := by
  induction H with
  | atom => exact Nat.zero_le _
  | @join p k h c arity wire child hs ih =>
    change (∑ i, ((child i).copiedRows + (child i).rows)) ≤ (k+1)*∑ i, (child i).rows
    rw [Finset.sum_add_distrib,Nat.succ_mul,Finset.mul_sum]
    exact Nat.add_le_add_right (Finset.sum_le_sum fun i _ => ih i) _

theorem nodes_pos (T : Tree F p) : 0 < T.nodes := by
  rw [← command_count]
  omega

/-- The constant 1016 is four generated words times the 254-step word scan.
`leafWork` covers initialization, pin generation and the terminal field scan
at its supplied per-record or per-private-bit cost. -/
def replayWork (T : Tree F p) (leafWork : ℕ) :=
  6 + 19*T.commands + 1016*T.copiedRows + leafWork*(T.nodes + T.rows + T.bits)

theorem replay_le {T : Tree F p} {k : ℕ} (H : Within k T) (leafWork : ℕ) :
    T.replayWork leafWork ≤ (25+1016*k+leafWork)*(T.nodes+T.rows+T.bits) := by
  let s := T.nodes+T.rows+T.bits
  have nle : T.commands ≤ s := by have := T.command_count; dsimp [s]; omega
  have pos : 1 ≤ s := by have := T.nodes_pos; dsimp [s]; omega
  have rle : T.rows ≤ s := by dsimp [s]; omega
  have copy := (rowCopies_le H).trans (Nat.mul_le_mul_left k rle)
  have a := Nat.mul_le_mul_left 19 nle
  have b := Nat.mul_le_mul_left 1016 copy
  have q := Nat.mul_le_mul_left 6 pos
  change 6+19*T.commands+1016*T.copiedRows+leafWork*s ≤ (25+1016*k+leafWork)*s
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- Compact per-cell score for the final greedy partition. In addition to
postorder replay and initialization, the score reserves ten thousand steps
per original record or hidden bit for fixed-size padding and field evaluation. -/
def scheduledWork (T : Tree F p) (k setup : ℕ) :=
  (10000 + 25 + 1016*k + setup) * (T.nodes+T.rows+T.bits)

theorem scheduledWork_covers {T : Tree F p} {k : ℕ} (H : Within k T) (setup : ℕ) :
    T.replayWork setup + 10000*(T.rows+T.bits) ≤ T.scheduledWork k setup := by
  have h := replay_le H setup
  have reserve := Nat.mul_le_mul_left 10000 (show T.rows+T.bits ≤ T.nodes+T.rows+T.bits by omega)
  unfold scheduledWork
  rw [show 10000+25+1016*k+setup = (25+1016*k+setup)+10000 by omega, Nat.add_mul]
  omega

end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
