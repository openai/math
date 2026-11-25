import OAI.Hierarchy.DescentTerminalPassNames
import OAI.Hierarchy.DescentTerminalActorRepack

namespace OAI
/-! # Exact instruction and clock costs of the population and occupation passes -/
namespace Hierarchy.DescentTerminalPriorNames
open ProtocolRAM DescentSIMDLookup DescentTerminalPointerDigits DescentColonies.SplitRAM
open DescentStaticWordColumn (names names_mount names_seq)
open DescentTerminalPrimitiveNames (readNames schedule_names)
noncomputable section

private theorem total_work {I : Type*} (f : I → Expr) (xs : List I) (one : ∀ i, (f i).work = 19) :
    (total f xs).work = 1 + 20 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [total, Expr.work, one, ih, List.length_cons, Nat.mul_succ]
    omega

/-- Every block runs the same expression shape. Different blocks can read different source banks. -/
private theorem scans {B : ℕ} (K origin H : ℕ) (field : Fin B → Expr)
    (uniform : ∀ i, (field i).work = K) :
    readNames (Gather.reads origin H field) = B * (11 + 4 * K) ∧
    clock (Gather.reads origin H field) = 4 + B * (4 + H * (2 * K + 4)) := by
  have work (j : ℕ) (hj : j < B) : (Gather.expression field j).work = K := by
    simpa only [Gather.expression, dite_eq_left hj] using uniform ⟨j, hj⟩
  have runs (start n : ℕ) (within : start + n ≤ B) :
      let ps := DescentPackedFlowBatch.passes origin H H (Gather.expression field) start n
      readNames ps = n * (11 + 4 * K) ∧
        clock ps = 4 + n * (4 + H * (2 * K + 4)) := by
    dsimp only
    induction n generalizing start with
    | zero => simp [DescentPackedFlowBatch.passes, readNames, clock]
    | succ n ih =>
      have tail := ih (start + 1) (by omega)
      have current := work start (by omega)
      simp only [DescentPackedFlowBatch.passes, readNames, clock, Pass.clock, current, tail.1,
        tail.2, Nat.succ_mul]
      constructor <;> omega
  exact runs 0 B (by omega)

section Population
open DescentTerminalPopulation.RAM
variable {B : ℕ} (w H G M a b c lo : ℕ) (old : Fin B → Bank) (ext : Bank)
local notation "J" => chunks G M
local notation "fee" => lease H G M a c lo
local notation "fields" => fun x => body H G M a c lo (old x) ext

theorem population_work (x : Fin B) : (fields x).work = 14 + 20 * J := by
  have each := total_work (bit H G M a c lo (old x)) (List.finRange J) (fun _ => rfl)
  simp only [body, Expr.work, each, List.length_finRange]
  omega

/-- Includes all literal installation instructions, all block scans, and their empty tail. -/
theorem population : names (issue H G M a b c lo old ext w) =
      15 * (fee + 1) + 15 + B * (67 + 80 * J) ∧
    ticks H G M a c lo old ext = 8 + 10 * fee + B * (4 + H * (32 + 40 * J)) := by
  obtain ⟨words, time⟩ := scans (14 + 20 * J) (lo + fee) H fields
    (population_work H G M a c lo old ext)
  constructor
  · simp only [issue, setup, names_seq, names_mount, schedule_names, words]; ring
  · simp only [ticks, time]; ring

end Population

section Occupation
open DescentTerminalActorRepack
variable {B a : ℕ} (pick : Fin B → Cell a → Cell 1) (w H G M lo : ℕ) (src : Fin B → Bank)
local notation "J" => chunks G M
local notation "fee" => count H G M a B lo
local notation "fields" => emit H G M a lo src

theorem actor_work (x : Fin B) : (fields x).work = 1 + 20 * J := by
  simpa only [emit, List.length_finRange] using
    total_work (field H G M a lo src x) (List.finRange J) (fun _ => rfl)

/-- This also covers the projection of a shared mask and independent one-bit block columns. -/
theorem actors : names (DescentTerminalActorRepack.program pick H G M lo src w) =
      15 * (fee + 1) + 15 + B * (15 + 80 * J) ∧
    DescentTerminalActorRepack.ticks (a := a) H G M lo src =
      8 + 10 * fee + B * (4 + H * (6 + 40 * J)) := by
  obtain ⟨words, time⟩ := scans (1 + 20 * J) (lo + fee) H fields (actor_work H G M lo src)
  constructor
  · simp only [DescentTerminalActorRepack.program, names_seq, names_mount, schedule_names, words]; ring
  · simp only [DescentTerminalActorRepack.ticks, time]; ring

end Occupation

variable {B aa : ℕ} (w H G M a b c lo M' next : ℕ)
    (old : Fin B → Bank) (ext : Bank) (pick : Fin B → Cell aa → Cell 1) (src : Fin B → Bank)
local notation "pfee" => DescentTerminalPopulation.RAM.lease H G M a c lo
local notation "afee" => DescentTerminalActorRepack.count H G M' aa B next
local notation "p" => DescentTerminalPopulation.RAM.issue H G M a b c lo old ext w
local notation "r" => DescentTerminalActorRepack.program pick H G M' next src w
local notation "parts" => chunks G M + chunks G M'

/-- The two native predecessors may store different numbers of group lanes in each source word. -/
theorem pair : names ((p).seq r) =
      60 + 15 * (pfee + afee) + B * (82 + 80 * parts) ∧
    DescentTerminalPopulation.RAM.ticks H G M a c lo old ext +
      DescentTerminalActorRepack.ticks (a := aa) H G M' next src =
      16 + 10 * (pfee + afee) + B * (8 + H * (38 + 40 * parts)) := by
  obtain ⟨popNames, popTime⟩ := population w H G M a b c lo old ext
  obtain ⟨actorNames, actorTime⟩ := actors pick w H G M' next src
  constructor
  · rw [names_seq, popNames, actorNames]; ring
  · rw [popTime, actorTime]; ring

end
end Hierarchy.DescentTerminalPriorNames

end OAI
