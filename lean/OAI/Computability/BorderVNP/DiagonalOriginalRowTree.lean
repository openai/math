import OAI.Computability.BorderVNP.ShortenAdaptiveFlatten

/-! # Fixed numeric names of original ports in a physical row history

A combining node preserves a child's original port row with a fixed offset.
The history may change the physical state and the identities of all newly
allocated rows. The original port row is nevertheless a sum of the offsets
of its public child digits and its bottom row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Crossing Shortening Adaptive

variable {k b D : ℕ} {A : ℕ → Type*} {P : Type} {bits : P → ℕ}
    (S : System k b A)
    (layout : ∀ n, A n → Network D (Port k P n) (width bits k n))
    (cap : ℕ → ℕ) (offset : ℕ → Fin k → ℕ)

/-- The actual sparse rows produced by one attained histogram. Original
child ports keep their rows inside the child's public rectangle. -/
structure Step where
  /-- Build the successor embedding from the incoming physical site rows. -/
  emit : ∀ n (hn : n < b) (c : Fin k → A n)
    (_ : ∀ j, (layout n (c j)).Site ↪ Fin (cap n)) (q : (S.choose n hn c).Index),
    (layout (n+1) ((S.choose n hn c).term q)).Site ↪ Fin (cap (n+1))
  /-- Read the numeric row of the physical successor at an original child port. -/
  atPort : ∀ n hn c ids q (j : Fin k) (p : Port k P n),
    (emit n hn c ids q ((layout (n+1) ((S.choose n hn c).term q)).attach (j,p))).val =
      offset n j + (ids j ((layout n (c j)).attach p)).val

/-- The actual physical state at a selected history index. -/
noncomputable def state (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (q : (S.histories n hn a).Index) := (S.layer n).state ((S.histories n hn a).term q)

variable {S layout cap offset}
variable (step : Step S layout cap offset)

/-- Real sparse site rows after a history, starting from the given physical bottom rows. -/
noncomputable def historyRows :
    (n : ℕ) → (hn : n ≤ b) → (flat : Fin (k^n) → A 0) →
    (∀ i, (layout 0 (flat i)).Site ↪ Fin (cap 0)) →
    (q : (S.histories n hn (leavesEquiv k (A 0) n flat)).Index) →
    (layout n (state S n hn (leavesEquiv k (A 0) n flat) q)).Site ↪ Fin (cap n)
  | 0, _, _, bottom, _ => bottom 0
  | n+1, hn, flat, bottom, q => by
    let hl := Nat.lt_of_succ_le hn
    let child := fun j : Fin k => fun i => flat (copyIndex k n (j,i))
    let c := fun j : Fin k => state S n hl.le (leavesEquiv k (A 0) n (child j)) (q.1 j)
    exact step.emit n hl c (fun j => historyRows n hl.le (child j)
      (fun i => bottom (copyIndex k n (j,i))) (q.1 j)) q.2

/-- Public offsets of the digits of a leaf number. Only the padded level
capacities and the row-major leaf ordinal enter this function. -/
def flatOffset (offset : ℕ → Fin k → ℕ) : (n : ℕ) → Fin (k^n) → ℕ
  | 0, _ => 0
  | n+1, u =>
    let d := (copyIndex k n).symm u
    offset n d.1 + flatOffset offset n d.2

/-- A leaf address is computed by placing its child rectangle at the public
offset and then applying the same lookup to the remaining digits. -/
theorem flatOffset_succ (offset : ℕ → Fin k → ℕ) (n : ℕ) (j : Fin k) (u : Fin (k^n)) :
    flatOffset offset (n+1) (copyIndex k n (j,u)) = offset n j + flatOffset offset n u := by
  simp only [flatOffset,Equiv.symm_apply_apply]

/-- The stable physical row at every original port is exactly its bottom
site number plus the public digit offsets. This holds for all actual profiles. -/
theorem historyRows_attach (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (bottom : ∀ i, (layout 0 (flat i)).Site ↪ Fin (cap 0))
    (q : (S.histories n hn (leavesEquiv k (A 0) n flat)).Index) (p : Port k P n) :
    let key := portEquiv k P n p
    (historyRows step n hn flat bottom q
      ((layout n (state S n hn (leavesEquiv k (A 0) n flat) q)).attach p)).val =
      flatOffset offset n key.1 + (bottom key.1 ((layout 0 (flat key.1)).attach key.2)).val := by
  induction n with
  | zero => exact (Nat.zero_add _).symm
  | succ n ih =>
    rcases p with ⟨j,p⟩
    let hl := Nat.lt_of_succ_le hn
    let child := fun u : Fin k => fun i => flat (copyIndex k n (u,i))
    let c := fun u : Fin k => state S n hl.le (leavesEquiv k (A 0) n (child u)) (q.1 u)
    let ids := fun u : Fin k => historyRows step n hl.le (child u)
      (fun i => bottom (copyIndex k n (u,i))) (q.1 u)
    have hs := step.atPort n hl c ids q.2 j p
    have hc := ih hl.le (child j) (fun i => bottom (copyIndex k n (j,i))) (q.1 j) p
    dsimp only at hc ⊢
    rw [portEquiv_succ,flatOffset_succ]
    exact hs.trans ((congrArg (offset n j + ·) hc).trans (Nat.add_assoc ..).symm)

/-- Reading a flattened port of the terminal pack uses the fixed arithmetic
lookup of its flat leaf number, followed by the original bottom site row. -/
theorem flat_attach (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (bottom : ∀ i, (layout 0 (flat i)).Site ↪ Fin (cap 0))
    (q : (S.histories n hn (leavesEquiv k (A 0) n flat)).Index) (u : Fin (k^n)) (p : P) :
    (historyRows step n hn flat bottom q
      ((layout n (state S n hn (leavesEquiv k (A 0) n flat) q)).attach ((portEquiv k P n).symm (u,p)))).val =
      flatOffset offset n u + (bottom u ((layout 0 (flat u)).attach p)).val := by
  let name (key : Fin (k^n) × P) :=
    flatOffset offset n key.1 + (bottom key.1 ((layout 0 (flat key.1)).attach key.2)).val
  exact (historyRows_attach step n hn flat bottom q ((portEquiv k P n).symm (u,p))).trans
    (congrArg name ((portEquiv k P n).apply_symm_apply (u,p)))

variable (S) (read : ∀ n, A n → Port k P n → ℕ) (offset)
    (next : ∀ n (hn : n < b) c (q : (S.choose n hn c).Index) j p,
      read (n+1) ((S.choose n hn c).term q) (j,p) = offset n j + read n (c j) p)

include next in
/-- A row read directly from each complete state follows the fixed child
offsets down its attained history. The original leaves may have different
physical layouts and assigned row numbers. -/
theorem assignedRows (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (q : (S.histories n hn (leavesEquiv k _ n flat)).Index) (p : Port k P n) :
    let z := portEquiv k P n p
    read n (state S n hn (leavesEquiv k _ n flat) q) p =
      flatOffset offset n z.1 + read 0 (flat z.1) z.2 := by
  induction n with
  | zero => exact (Nat.zero_add _).symm
  | succ n ih =>
    obtain ⟨j,p⟩ := p
    let hl := Nat.lt_of_succ_le hn
    let child := fun j : Fin k => fun u => flat (copyIndex k n (j,u))
    let c := fun j => state S n hl.le (leavesEquiv k _ n (child j)) (q.1 j)
    have hs := next n hl c q.2 j p
    have hc := ih hl.le (child j) (q.1 j) p
    dsimp only at hc ⊢
    rw [portEquiv_succ,flatOffset_succ]
    exact hs.trans ((congrArg (offset n j + ·) hc).trans (Nat.add_assoc ..).symm)

include next in
/-- The final row in the physical history on the specified flat leaves,
read using the public copy number and original port. -/
theorem assignedRows_flat (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (q : (S.histories n hn (leavesEquiv k _ n flat)).Index) (z : Fin (k^n) × P) :
    read n (state S n hn (leavesEquiv k _ n flat) q) ((portEquiv k P n).symm z) =
      flatOffset offset n z.1 + read 0 (flat z.1) z.2 :=
  (assignedRows S offset read next n hn flat q ((portEquiv k P n).symm z)).trans
    (congrArg (fun y : Fin (k^n) × P => flatOffset offset n y.1 + read 0 (flat y.1) y.2)
      ((portEquiv k P n).apply_symm_apply z))

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
