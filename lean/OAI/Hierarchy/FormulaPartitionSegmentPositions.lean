import OAI.Hierarchy.FormulaPartitionSegments
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Splitting a fixed gate path at its marked positions -/

namespace Hierarchy.FormulaPartition
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V] [Fintype V]

/-- Gates are indexed from zero. A step at time `i` arrives at time `i+1`. -/
def intervalSteps (ks : ℕ → GuardedStep V τ F) (start len : ℕ) :=
  (List.range' start len).map ks

def applyPin (ks : ℕ → GuardedStep V τ F) (pin : ℕ → Finset V → Prop) (i : ℕ) :
    GuardedStep V τ F :=
  ((ks i).1,fun S T => (ks i).2 S T ∧ pin (i+1) T)

omit [Fintype V] in
theorem intervalSteps_append (ks : ℕ → GuardedStep V τ F) (a m n : ℕ) :
    intervalSteps ks a (m+n) = intervalSteps ks a m ++ intervalSteps ks (a+m) n := by
  simp only [intervalSteps,← List.map_append,List.range'_append_1]

private theorem split_interval (ks : ℕ → GuardedStep V τ F) {a b c : ℕ}
    (ab : a≤b) (bc : b≤c) (x : ∀v,τ v) (S : Finset V) (tip : Finset V→F) :
    walk (intervalSteps ks a (c-a)) x S tip =
      walk (intervalSteps ks a (b-a)) x S (fun U=>walk (intervalSteps ks b (c-b)) x U tip) := by
  rw [show c-a=(b-a)+(c-b) by omega,intervalSteps_append,show a+(b-a)=b by omega,walk_append]

theorem walk_no_pins (ks : ℕ → GuardedStep V τ F) (pin : ℕ → Finset V → Prop)
    (start len : ℕ) (clear : ∀ i, start < i → i≤start+len → ∀ T,pin i T)
    (x : ∀v,τ v) (S : Finset V) (tip : Finset V→F) :
    walk (intervalSteps (applyPin ks pin) start len) x S tip =
      walk (intervalSteps ks start len) x S tip := by
  induction len generalizing start S with
  | zero => rfl
  | succ n ih =>
    simp only [intervalSteps,List.range'_succ,List.map_cons,walk,applyPin]
    apply Finset.sum_congr rfl
    intro T _
    simp only [clear (start+1) (by omega) (by omega) T,and_true]
    rw [show walk ((List.range' (start+1) n).map (applyPin ks pin)) x T tip =
        walk ((List.range' (start+1) n).map ks) x T tip from
      ih (start+1) (fun i h1 h2 => clear i (by omega) (by omega)) T]

private theorem walk_last_pin (ks : ℕ → GuardedStep V τ F) (pin : ℕ → Finset V → Prop)
    {a b : ℕ} (ab : a<b) (Q : Finset V)
    (clear : ∀ i, a < i → i<b → ∀ T,pin i T) (endPin : ∀ T,pin b T ↔ T=Q)
    (x : ∀v,τ v) (S : Finset V) (tip : Finset V→F) :
    walk (intervalSteps (applyPin ks pin) a (b-a)) x S tip =
      walk (intervalSteps ks a (b-a)) x S (fun T=>if T=Q then tip T else 0) := by
  rw [split_interval (applyPin ks pin) (b:=b-1) (by omega) (by omega),
      split_interval ks (b:=b-1) (by omega) (by omega),
      walk_no_pins ks pin a ((b-1)-a) (fun i h1 h2 => clear i h1 (by omega))]
  apply congrArg (walk _ x S)
  funext U
  rw [show b-(b-1)=1 by omega]
  have one (z : ℕ → GuardedStep V τ F) : intervalSteps z (b-1) 1 = [z (b-1)] := rfl
  simp only [one,walk,applyPin]
  apply Finset.sum_congr rfl
  intro T _
  have test : pin (b-1+1) T ↔ T=Q := by simpa only [show b-1+1=b by omega] using endPin T
  by_cases hg : (ks (b-1)).2 U T
  · by_cases ht : T=Q
    · have on : (ks (b-1)).2 U T ∧ pin (b-1+1) T := ⟨hg,test.mpr ht⟩
      rw [ite_eq_left on,ite_eq_left hg,ite_eq_left ht]
    · have off : ¬ ((ks (b-1)).2 U T ∧ pin (b-1+1) T) := fun h => ht (test.mp h.2)
      rw [ite_eq_right off,ite_eq_left hg,ite_eq_right ht,mul_zero]
  · have off : ¬ ((ks (b-1)).2 U T ∧ pin (b-1+1) T) := fun h => hg h.1
    rw [ite_eq_right off,ite_eq_right hg]

/-- The j-th actual portion of the path runs from position p(j) up to p(j+1). -/
def positionSegments {t : ℕ} (ks : ℕ → GuardedStep V τ F)
    (p : Fin (t+1) → ℕ) (Q : Fin (t+1) → Finset V) : List (MarkedSegment V τ F) :=
  List.ofFn fun j : Fin t =>
    (intervalSteps ks (p j.castSucc) (p j.succ-p j.castSucc), Q j.succ)

/-- Pinning globally at exactly the designated times gives the same path sum
as contracting the successive marked segments. -/
theorem walk_positions {t : ℕ} (ks : ℕ → GuardedStep V τ F) (pin : ℕ → Finset V → Prop)
    (p : Fin (t+1) → ℕ) (ordered : StrictMono p) (Q : Fin (t+1) → Finset V)
    (clear : ∀ j : Fin t, ∀ i, p j.castSucc < i → i<p j.succ → ∀ T,pin i T)
    (endPin : ∀ j : Fin t, ∀ T,pin (p j.succ) T ↔ T=Q j.succ)
    (x : ∀v,τ v) (S : Finset V) (tip : Finset V→F) :
    walk (intervalSteps (applyPin ks pin) (p 0) (p (Fin.last t)-p 0)) x S tip =
      markedWalk (positionSegments ks p Q) x S tip := by
  induction t generalizing S with
  | zero => simp [positionSegments,intervalSteps,markedWalk,walk,Fin.last_zero]
  | succ t ih =>
    let tail := fun j : Fin (t+1) => p j.succ
    let rest := fun j : Fin (t+1) => Q j.succ
    have first : p 0 < tail 0 := ordered (by exact Fin.zero_lt_one)
    have last : tail 0 ≤ p (Fin.last (t+1)) := ordered.monotone (Fin.le_last _)
    have next (U : Finset V) :
        walk (intervalSteps (applyPin ks pin) (tail 0) (p (Fin.last (t+1))-tail 0)) x U tip =
          markedWalk (positionSegments ks tail rest) x U tip := by
      exact ih tail (fun _ _ lt => ordered (Fin.succ_lt_succ_iff.mpr lt)) rest
        (fun j => clear j.succ) (fun j => endPin j.succ) U
    rw [split_interval _ first.le last]
    simp_rw [next]
    rw [walk_last_pin _ _ first (rest 0) (clear 0) (endPin 0)]
    have pieces : positionSegments ks p Q =
        (intervalSteps ks (p 0) (tail 0-p 0),rest 0) :: positionSegments ks tail rest :=
      List.ofFn_succ
    rw [pieces]
    rfl

theorem markedWalk_position_prod {t : ℕ} (ks : ℕ → GuardedStep V τ F)
    (p : Fin (t+1) → ℕ) (Q : Fin (t+1) → Finset V) (x : ∀v,τ v) (tip : Finset V → F) :
    markedWalk (positionSegments ks p Q) x (Q 0) tip =
      (∏ j : Fin t, segmentValue (intervalSteps ks (p j.castSucc) (p j.succ-p j.castSucc))
        x (Q j.castSucc) (Q j.succ)) * tip (Q (Fin.last t)) := by
  induction t with
  | zero => simp [positionSegments,markedWalk,Fin.last_zero]
  | succ t ih =>
    rw [positionSegments,List.ofFn_succ,Fin.prod_univ_succ]
    change walk _ x (Q 0) (fun U => if U=Q (Fin.succ 0) then
        markedWalk (positionSegments ks (fun j=>p j.succ) (fun j=>Q j.succ)) x U tip else 0) = _
    rw [walk_pin,ih (fun j=>p j.succ) (fun j=>Q j.succ),mul_assoc]
    simp only [Fin.succ_last,Fin.succ_castSucc,Fin.castSucc_zero]

theorem full_walk_position_prod {t len : ℕ} (ks : ℕ → GuardedStep V τ F) (pin : ℕ → Finset V → Prop)
    (p : Fin (t+1) → ℕ) (ordered : StrictMono p) (Q : Fin (t+1) → Finset V)
    (start : p 0 = 0) (stop : p (Fin.last t) ≤ len)
    (clear : ∀ j : Fin t, ∀ i, p j.castSucc < i → i<p j.succ → ∀ T,pin i T)
    (endPin : ∀ j : Fin t, ∀ T,pin (p j.succ) T ↔ T=Q j.succ)
    (x : ∀v,τ v) (tip : Finset V → F) :
    walk (intervalSteps (applyPin ks pin) 0 len) x (Q 0) tip =
      (∏ j : Fin t, segmentValue (intervalSteps ks (p j.castSucc) (p j.succ-p j.castSucc))
          x (Q j.castSucc) (Q j.succ)) *
        walk (intervalSteps (applyPin ks pin) (p (Fin.last t)) (len-p (Fin.last t))) x (Q (Fin.last t)) tip := by
  have split := split_interval (applyPin ks pin) (a:=p 0) (b:=p (Fin.last t)) (c:=len)
    (ordered.monotone (Fin.le_last _)) stop x (Q 0) tip
  rw [walk_positions ks pin p ordered Q clear endPin,markedWalk_position_prod] at split
  simpa only [start,Nat.sub_zero] using split


end
end Hierarchy.FormulaPartition

end OAI
