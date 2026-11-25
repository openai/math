import OAI.Optimization.LinearProgramming.RAM.Execution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A single RAM program for evaluating the affine forms returned by the minor oracle. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM Finset
open scoped BigOperators

/-- Input is the constant in register 0, two scratch cells, and coefficient/argument pairs
in consecutive registers from address 3. Index register 0 holds the number of pairs. -/
def affineEvalProgram : Program :=
  [.addrConst 2 3, .branchAddrLT 1 0 2 10, .load 1 2, .incr 2 2, .load 2 2,
   .mul 1 1 2, .add 0 0 1, .incr 2 2, .decr 0 0, .jump 1, .halt 0]

private def header {α : Type*} (a b c : α) (rest : ℕ → α) : ℕ → α
  | 0 => a
  | 1 => b
  | 2 => c
  | k + 3 => rest k

private theorem set0 {α : Type*} (a b c x : α) (rest : ℕ → α) :
    Function.update (header a b c rest) 0 x = header x b c rest := by
  funext i; match i with | 0 | 1 | 2 | _ + 3 => rfl

private theorem set1 {α : Type*} (a b c x : α) (rest : ℕ → α) :
    Function.update (header a b c rest) 1 x = header a x c rest := by
  funext i; match i with | 0 | 1 | 2 | _ + 3 => rfl

private theorem set2 {α : Type*} (a b c x : α) (rest : ℕ → α) :
    Function.update (header a b c rest) 2 x = header a b x rest := by
  funext i; match i with | 0 | 1 | 2 | _ + 3 => rfl

private def machineFrame (pc rem cursor : ℕ) (acc a x : ℚ) (tape : ℕ → ℚ) : State ℚ :=
  ⟨pc, header acc a x tape, header rem 0 cursor (fun _ => 0), none⟩

private theorem frameBound {H : ℕ} {acc a x : ℚ} {t : ℕ → ℚ}
    (ht : ∀ i, ratBits (t i) ≤ H) (hc : ratBits acc ≤ H) (ha : ratBits a ≤ H)
    (hx : ratBits x ≤ H) (pc rem cur : ℕ) : scalarBound H (machineFrame pc rem cur acc a x t) := by
  intro i
  match i with
  | 0 => exact hc
  | 1 => exact ha
  | 2 => exact hx
  | k+3 => exact ht k

private theorem loopStep {H : ℕ} (n k : ℕ) (acc a x : ℚ) (t : ℕ → ℚ)
    (ht : ∀ i, ratBits (t i) ≤ H) (hc : ratBits acc ≤ H) (ha : ratBits a ≤ H)
    (hx : ratBits x ≤ H) (hprod : ratBits (t k * t (k+1)) ≤ H)
    (hnext : ratBits (acc + t k * t (k+1)) ≤ H) :
    Execution affineEvalProgram (scalarBound H)
      (machineFrame 1 (n+1) (k+3) acc a x t) 9
      (machineFrame 1 n ((k+2)+3) (acc+t k*t (k+1)) (t k*t (k+1)) (t (k+1)) t) := by
  let prod := t k * t (k+1)
  let new := acc + prod
  have s1 : step affineEvalProgram (machineFrame 1 (n+1) (k+3) acc a x t) =
      some (machineFrame 2 (n+1) (k+3) acc a x t) := by
    change some (machineFrame (if 0<n+1 then 2 else 10) _ _ _ _ _ _) = _
    simp
  have s2 : step affineEvalProgram (machineFrame 2 (n+1) (k+3) acc a x t) =
      some (machineFrame 3 (n+1) (k+3) acc (t k) x t) := by
    change some (State.mk _ (Function.update (header acc a x t) 1 (t k)) _ none) = _
    rw [set1]; rfl
  have s3 : step affineEvalProgram (machineFrame 3 (n+1) (k+3) acc (t k) x t) =
      some (machineFrame 4 (n+1) ((k+1)+3) acc (t k) x t) := by
    change some (State.mk _ _ (Function.update (header (n+1) 0 (k+3) _) 2 (k+3+1)) none) = _
    rw [set2]; rfl
  have s4 : step affineEvalProgram (machineFrame 4 (n+1) ((k+1)+3) acc (t k) x t) =
      some (machineFrame 5 (n+1) ((k+1)+3) acc (t k) (t (k+1)) t) := by
    change some (State.mk _ (Function.update (header acc (t k) x t) 2 (t (k+1))) _ none) = _
    rw [set2]; rfl
  have s5 : step affineEvalProgram (machineFrame 5 (n+1) ((k+1)+3) acc (t k) (t (k+1)) t) =
      some (machineFrame 6 (n+1) ((k+1)+3) acc prod (t (k+1)) t) := by
    change some (State.mk _ (Function.update (header acc (t k) (t (k+1)) t) 1 prod) _ none) = _
    rw [set1]; rfl
  have s6 : step affineEvalProgram (machineFrame 6 (n+1) ((k+1)+3) acc prod (t (k+1)) t) =
      some (machineFrame 7 (n+1) ((k+1)+3) new prod (t (k+1)) t) := by
    change some (State.mk _ (Function.update (header acc prod (t (k+1)) t) 0 new) _ none) = _
    rw [set0]; rfl
  have s7 : step affineEvalProgram (machineFrame 7 (n+1) ((k+1)+3) new prod (t (k+1)) t) =
      some (machineFrame 8 (n+1) ((k+2)+3) new prod (t (k+1)) t) := by
    change some (State.mk _ _ (Function.update (header (n+1) 0 ((k+1)+3) _) 2 ((k+1)+3+1)) none) = _
    rw [set2]; rfl
  have s8 : step affineEvalProgram (machineFrame 8 (n+1) ((k+2)+3) new prod (t (k+1)) t) =
      some (machineFrame 9 n ((k+2)+3) new prod (t (k+1)) t) := by
    change some (State.mk _ _ (Function.update (header (n+1) 0 ((k+2)+3) _) 0 n) none) = _
    rw [set0]; rfl
  have s9 : step affineEvalProgram (machineFrame 9 n ((k+2)+3) new prod (t (k+1)) t) =
      some (machineFrame 1 n ((k+2)+3) new prod (t (k+1)) t) := rfl
  exact .next (frameBound ht hc ha hx 1 (n+1) (k+3)) s1 <|
    .next (frameBound ht hc ha hx 2 (n+1) (k+3)) s2 <|
    .next (frameBound ht hc (ht k) hx 3 (n+1) (k+3)) s3 <|
    .next (frameBound ht hc (ht k) hx 4 (n+1) ((k+1)+3)) s4 <|
    .next (frameBound ht hc (ht k) (ht (k+1)) 5 (n+1) ((k+1)+3)) s5 <|
    .next (frameBound ht hc hprod (ht (k+1)) 6 (n+1) ((k+1)+3)) s6 <|
    .next (frameBound ht hnext hprod (ht (k+1)) 7 (n+1) ((k+1)+3)) s7 <|
    .next (frameBound ht hnext hprod (ht (k+1)) 8 (n+1) ((k+2)+3)) s8 <|
    .next (frameBound ht hnext hprod (ht (k+1)) 9 n ((k+2)+3)) s9 <|
    .done _ (frameBound ht hnext hprod (ht (k+1)) 1 n ((k+2)+3))

/-- The value in the accumulator after the first k coefficient/argument pairs. -/
def affinePrefix (e : ℚ) (t : ℕ → ℚ) (k : ℕ) : ℚ :=
  e + ∑ i ∈ range k, t (2*i) * t (2*i+1)

private theorem loopIterate {H : ℕ} (e : ℚ) (t : ℕ → ℚ) (n : ℕ)
    (ht : ∀ i, ratBits (t i) ≤ H) (hzero : ratBits 0 ≤ H)
    (hsum : ∀ k ≤ n, ratBits (affinePrefix e t k) ≤ H)
    (hprod : ∀ k < n, ratBits (t (2*k)*t (2*k+1)) ≤ H) :
    ∀ k ≤ n, ∃ a x, Execution affineEvalProgram (scalarBound H)
      (machineFrame 1 n 3 e 0 0 t) (9*k)
      (machineFrame 1 (n-k) (2*k+3) (affinePrefix e t k) a x t) ∧
      ratBits a ≤ H ∧ ratBits x ≤ H := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, 0, by simpa [affinePrefix] using
      (Execution.done (p := affineEvalProgram) _ (frameBound ht (by simpa [affinePrefix] using hsum 0 (Nat.zero_le _)) hzero hzero 1 n 3)), hzero, hzero⟩
  | succ k ih =>
    intro hkn
    obtain ⟨a,x,hprev,ha,hx⟩ := ih (by omega)
    have hrem : n-k = (n-(k+1))+1 := by omega
    have heq : affinePrefix e t (k+1) =
        affinePrefix e t k + t (2*k)*t (2*k+1) := by
      simp [affinePrefix, Finset.sum_range_succ, add_assoc]
    have hit := loopStep (n-(k+1)) (2*k) (affinePrefix e t k) a x t ht (hsum k (by omega)) ha hx
      (hprod k (by omega)) (heq ▸ hsum (k+1) hkn)
    rw [hrem] at hprev
    refine ⟨_, _, ?_, hprod k (by omega), ht (2*k+1)⟩
    simpa only [Nat.mul_succ, ← heq] using hprev.append hit

/-- Addresses outside the supplied scalar input read as zero, as in RAM.start. -/
def affineTapeRead (s : List ℚ) (i : ℕ) : ℚ := s[i]?.getD 0

/-- The complete single-program trace, including both address initialization and halt.
Every intermediate register is checked under the supplied prefix/product size bounds. -/
theorem affineProgram_trace (e : ℚ) (payload : List ℚ) (n H : ℕ)
    (ht : ∀ i, ratBits (affineTapeRead payload i) ≤ H) (hzero : ratBits 0 ≤ H)
    (hsum : ∀ k ≤ n, ratBits (affinePrefix e (affineTapeRead payload) k) ≤ H)
    (hprod : ∀ k < n, ratBits (affineTapeRead payload (2*k) * affineTapeRead payload (2*k+1)) ≤ H) :
    ∃ t : Fin (9*n+3+1) → State ℚ,
      Trace affineEvalProgram (start [n] (e :: 0 :: 0 :: payload)) (9*n+3) t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 0 = affinePrefix e (affineTapeRead payload) n ∧
      ∀ i, scalarBound H (t i) := by
  let f := affineTapeRead payload
  have he : ratBits e ≤ H := by simpa [affinePrefix] using hsum 0 (Nat.zero_le _)
  have hstart : start [n] (e :: 0 :: 0 :: payload) = machineFrame 0 n 0 e 0 0 f := by
    unfold start machineFrame
    congr 1 <;> funext i <;> match i with | 0 | 1 | 2 | _+3 => rfl
  have init : step affineEvalProgram (machineFrame 0 n 0 e 0 0 f) =
      some (machineFrame 1 n 3 e 0 0 f) := by
    change some (State.mk _ _ (Function.update (header n 0 0 _) 2 3) none) = _
    rw [set2]; rfl
  obtain ⟨a,x,hloop,ha,hx⟩ := loopIterate e f n ht hzero hsum hprod n le_rfl
  rw [Nat.sub_self] at hloop
  let value := affinePrefix e f n
  have hval : ratBits value ≤ H := hsum n le_rfl
  have close : step affineEvalProgram (machineFrame 1 0 (2*n+3) value a x f) =
      some (machineFrame 10 0 (2*n+3) value a x f) := rfl
  let last := {machineFrame 10 0 (2*n+3) value a x f with output := some 0}
  have halt : step affineEvalProgram (machineFrame 10 0 (2*n+3) value a x f) = some last := rfl
  have safeLast : scalarBound H last := frameBound ht hval ha hx 10 0 (2*n+3)
  have hfinal : Execution affineEvalProgram (scalarBound H) (machineFrame 1 0 (2*n+3) value a x f)
      2 last := .next (frameBound ht hval ha hx 1 0 (2*n+3)) close
      (.next (frameBound ht hval ha hx 10 0 (2*n+3)) halt (.done _ safeLast))
  have hall : Execution affineEvalProgram (scalarBound H) (start [n] (e::0::0::payload))
      (9*n+3) last := by
    rw [hstart]
    have h := Execution.next (frameBound ht he hzero hzero 0 n 0) init (hloop.append hfinal)
    exact h
  obtain ⟨t, htrace, htlast, hsafe⟩ := hall.to_trace
  exact ⟨t, htrace, htlast ▸ rfl, htlast ▸ rfl, hsafe⟩

end Compression
end LinearProgramming
end Optimization
end OAI
