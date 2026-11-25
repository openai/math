import OAI.Computability.NearSquareRoot.CommonAlphabetROMCellsTrace

/-!
# Charged transition traces of the two-copy program reader

All lengths below count physical transitions of the fixed interpreter rule. During a row
jump one ROM head reads a stream of unary ticks and the other scans forward on the table;
the number of scanned cells is charged even on a jump across many rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal

open IntegerMultiplication
variable {A I : Type} [Finite A] [Finite I]
variable (blank : A) (s : ℤ → Tag A I) (d : I → TM.Tape A) (b : Bool)

theorem seek_steps_bank (p q l : ℕ)
    (h : ∀ k < l, ¬ branchReads (fun i => (d i).view 0) (s (p+k : ℕ))) :
    During (TM.advance (rule blank)) (HasBank d) (conf s d b .seek p q) l (conf s d b .seek (p+l : ℕ) q) := by
  induction l with
  | zero => simpa using During.nil (s := TM.advance (rule blank)) (conf s d b .seek p q) (fun _ => rfl)
  | succ l ih =>
    refine During.trans (ih (fun k hk => h k (by omega))) (During.single ?_ (fun _ => rfl) (fun _ => rfl))
    simpa [add_assoc] using seek_next blank s d b (p+l : ℕ) q (h l (by omega))

theorem seek_steps (p q l : ℕ)
    (h : ∀ k < l, ¬ branchReads (fun i => (d i).view 0) (s (p+k : ℕ))) :
    Trace (TM.advance (rule blank)) (conf s d b .seek p q) l (conf s d b .seek (p+l : ℕ) q) :=
  (seek_steps_bank blank s d b p q l h).trace

theorem skip_steps_bank (p q l : ℕ)
    (h : ∀ k < l, s (q+k : ℕ) ≠ .row) :
    During (TM.advance (rule blank)) (HasBank d) (conf s d b .skip p q) l (conf s d b .skip p (q+l : ℕ)) := by
  induction l with
  | zero => simpa using During.nil (s := TM.advance (rule blank)) (conf s d b .skip p q) (fun _ => rfl)
  | succ l ih =>
    refine During.trans (ih (fun k hk => h k (by omega))) (During.single ?_ (fun _ => rfl) (fun _ => rfl))
    simpa [add_assoc] using skip_next blank s d b p (q+l : ℕ) (h l (by omega))

theorem skip_steps (p q l : ℕ)
    (h : ∀ k < l, s (q+k : ℕ) ≠ .row) :
    Trace (TM.advance (rule blank)) (conf s d b .skip p q) l (conf s d b .skip p (q+l : ℕ)) :=
  (skip_steps_bank blank s d b p q l h).trace

theorem rewind_steps_bank (p q : ℕ) (h : ∀ k : ℕ, 0 < k → k ≤ p → s k ≠ .origin) :
    During (TM.advance (rule blank)) (HasBank d) (conf s d b .rewind p q) p (conf s d b .rewind 0 q) := by
  induction p with
  | zero => exact .nil _ (fun _ => rfl)
  | succ p ih =>
    rw [Nat.add_comm p 1]
    apply During.cons (y := conf s d b .rewind p q) _ (fun _ => rfl) (ih (fun k hk hle => h k hk (by omega)))
    simpa [Nat.add_comm] using rewind_left blank s d b (p+1 : ℕ) q (h _ (by omega) le_rfl)

theorem rewind_steps (p q : ℕ) (h : ∀ k : ℕ, 0 < k → k ≤ p → s k ≠ .origin) :
    Trace (TM.advance (rule blank)) (conf s d b .rewind p q) p (conf s d b .rewind 0 q) :=
  (rewind_steps_bank blank s d b p q h).trace

/-- One unary tick selects the next row. The physical scan costs one step
per ROM cell plus one step for acknowledging the next row marker. -/
theorem jump_one_bank (p q u : ℕ) (hq : q < u) (ht : s p = .tick) (hu : s u = .row)
    (hgap : ∀ v : ℕ, q < v → v < u → s v ≠ .row) :
    During (TM.advance (rule blank)) (HasBank d) (conf s d b .dest p q) (u-q+1)
      (conf s d b .dest (p+1 : ℕ) u) := by
  let gap := u - (q+1)
  have hend : (q+1)+gap = u := by dsimp [gap]; omega
  have hg := skip_steps_bank blank s d b p (q+1) gap (fun k hk => hgap (q+1+k) (by omega) (by omega))
  rw [hend] at hg
  have h₁ : TM.advance (rule blank) (conf s d b .dest p q) =
      some (conf s d b .skip p (q+1 : ℕ)) := by simpa using dest_tick blank s d b p q ht
  have h₂ : TM.advance (rule blank) (conf s d b .skip p u) =
      some (conf s d b .dest (p+1 : ℕ) u) := by simpa using skip_row blank s d b p u hu
  convert (During.cons h₁ (fun _ => rfl) (During.trans hg (During.single h₂ (fun _ => rfl) (fun _ => rfl)))) using 1
  omega

theorem jump_one (p q u : ℕ) (hq : q < u) (ht : s p = .tick) (hu : s u = .row)
    (hgap : ∀ v : ℕ, q < v → v < u → s v ≠ .row) :
    Trace (TM.advance (rule blank)) (conf s d b .dest p q) (u-q+1)
      (conf s d b .dest (p+1 : ℕ) u) :=
  (jump_one_bank blank s d b p q u hq ht hu hgap).trace

/-- Successive unary ticks move the parked head from row zero to row `k`,
with a total time linear in the physical row address plus the unary length. -/
theorem jump_steps_bank (row : ℕ → ℕ) (p k : ℕ) (h₀ : row 0 = 1)
    (hinc : ∀ i < k, row i < row (i+1))
    (hr : ∀ i < k, s (row (i+1)) = .row)
    (hgap : ∀ i < k, ∀ v : ℕ, row i < v → v < row (i+1) → s v ≠ .row)
    (ht : ∀ i < k, s (p+i : ℕ) = .tick) :
    During (TM.advance (rule blank)) (HasBank d) (conf s d b .dest p 1)
      ((row k - 1) + k) (conf s d b .dest (p+k : ℕ) (row k)) := by
  induction k with
  | zero => simpa [h₀] using During.nil (s := TM.advance (rule blank)) (conf s d b .dest p 1) (fun _ => rfl : HasBank d _)
  | succ k ih =>
    have h₁ := ih (fun i hi => hinc i (by omega)) (fun i hi => hr i (by omega))
      (fun i hi => hgap i (by omega)) (fun i hi => ht i (by omega))
    have h₂ := jump_one_bank blank s d b (p+k) (row k) (row (k+1)) (hinc k (by omega))
      (ht k (by omega)) (hr k (by omega)) (hgap k (by omega))
    have hpos : 0 < row k := by
      cases k with
      | zero => omega
      | succ j => have := hinc j (by omega); omega
    have hlt := hinc k (by omega)
    convert During.trans h₁ h₂ using 1
    omega

theorem jump_steps (row : ℕ → ℕ) (p k : ℕ) (h₀ : row 0 = 1)
    (hinc : ∀ i < k, row i < row (i+1))
    (hr : ∀ i < k, s (row (i+1)) = .row)
    (hgap : ∀ i < k, ∀ v : ℕ, row i < v → v < row (i+1) → s v ≠ .row)
    (ht : ∀ i < k, s (p+i : ℕ) = .tick) :
    Trace (TM.advance (rule blank)) (conf s d b .dest p 1)
      ((row k - 1) + k) (conf s d b .dest (p+k : ℕ) (row k)) :=
  (jump_steps_bank blank s d b row p k h₀ hinc hr hgap ht).trace

end Universal

end NearSquareRoot
end Computability
end OAI
