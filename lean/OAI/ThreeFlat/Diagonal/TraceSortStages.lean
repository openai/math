import OAI.ThreeFlat.Diagonal.TraceSortSelect
import OAI.Computability.VPVNP.RAMSortCostLayout

namespace OAI
/-! # The two-track site's gate program for all bitonic phases -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMSort Computability.VPVNP.RAMMemory
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSlots TraceWords

variable {σ : Type*} {w d : ℕ}
abbrev Live (w : ℕ) := (Fin 2 × Fin 7 × Fin w) ⊕ Unit
abbrev StagePins (w d : ℕ) (σ : Type*) := ∀ s : Stage (1+d), Sends 1 d s (SlotAddr w σ)
abbrev StageData (w d : ℕ) := ∀ s : Stage (1+d), Sends 1 d s (Narrow w)

def ReadLive (hw : 2 ≤ w) (z : Live w → Bool) (cur : Fin 2 → Narrow w) : Prop :=
  ∀ i f j, z (.inl (i,f,j)) = bits (fields hw (cur i) f) j

def ownAddr (i : Fin 2) (f : Fin 7) (j : Fin w) : σ ⊕ Live w := .inr (.inl (i,f,j))

def sendAddr (pins : StagePins w d σ) (s : Stage (1+d))
    (h : 1 ≤ s.stride) (v : Fin (2^d)) (i : Fin 2) : SlotAddr w (σ ⊕ Live w) :=
  fun f j => .inl (pins s h v i f j)

def stepExpr (pins : StagePins w d σ) (s : Stage (1+d)) (v : Fin (2^d)) :
    Live w → Expr (σ ⊕ Live w)
  | .inl (i,f,j) => pick (lowOutput s v i) (ownAddr i) (other s v (sendAddr pins s) ownAddr i) f j
  | .inr _ => (Expr.input (.inr (.inr ()))).and
      (if h : 1 ≤ s.stride then allBits fun i => eqPort (ownAddr i) (sendAddr pins s h v i)
       else .const true)

variable [Fintype σ]

noncomputable def advance (f : Frame σ (Live w)) (pins : StagePins w d σ)
    (s : Stage (1+d)) (v : Fin (2^d)) : Frame σ (Live w) :=
  f.withInput.step (stepExpr pins s v)

theorem advance_eval (hw : 2 ≤ w) (frame : Frame σ (Live w)) (pins : StagePins w d σ)
    (send : StageData w d) (s : Stage (1+d)) (v : Fin (2^d)) (x : σ → Bool)
    (cur : Fin 2 → Narrow w) (hc : ReadLive hw (frame.eval x) cur)
    (hs : ∀ h u, u = v ∨ u = sourceSite s h v → ∀ i, ReadSlot hw x (pins s h u i) (send s h u i)) :
    ReadLive hw ((advance frame pins s v).eval x) (next s v (send s) cur) ∧
    (((advance frame pins s v).eval x (.inr ()) = true) ↔
       frame.eval x (.inr ()) = true ∧ ∀ h, send s h v = cur) := by
  let y := frame.withInput.eval x
  have ho (i) : ReadSlot hw y (ownAddr i) (cur i) := by
    intro f j
    simpa [y, ownAddr] using hc i f j
  have ht (h u) (near : u = v ∨ u = sourceSite s h v) (i) : ReadSlot hw y (sendAddr pins s h u i) (send s h u i) := by
    intro f j
    simpa [y, sendAddr] using hs h u near i f j
  constructor
  · intro i f j
    have hp : ReadSlot hw y (other s v (sendAddr pins s) ownAddr i) (other s v (send s) cur i) := by
      unfold other
      split
      · exact ht _ _ (.inr rfl) _
      · exact ho _
    simpa only [advance, Frame.step_eval, stepExpr, next] using
      pick_eval hw y (lowOutput s v i) _ _ _ _ (ho i) hp f j
  · simp only [advance, Frame.step_eval, stepExpr, Expr.eval, Frame.withInput_eval_inr,
      Bool.and_eq_true]
    apply and_congr_right
    intro _
    by_cases h : 1 ≤ s.stride
    · rw [dite_eq_left h, allBits_true]
      exact ⟨fun a _ => funext fun i => ((eqPort_eval hw y _ _ _ _ (ho i) (ht h v (.inl rfl) i)).mp (a i)).symm,
        fun a i => (eqPort_eval hw y _ _ _ _ (ho i) (ht h v (.inl rfl) i)).mpr (congrFun (a h) i).symm⟩
    · simp [h, Expr.eval]

theorem advance_size (frame : Frame σ (Live w)) (pins : StagePins w d σ)
    (s : Stage (1+d)) (v : Fin (2^d)) :
    (advance frame pins s v).size ≤ frame.size + (14*w+1)*(500*(w+1)) := by
  have hb (i : Live w) : (stepExpr pins s v i).size ≤ 500*(w+1) := by
    rcases i with ⟨i,f,j⟩ | ⟨⟩
    · apply pick_size
    · by_cases h : 1 ≤ s.stride
      · have z := allBits_size_le (fun i : Fin 2 => eqPort (ownAddr i) (sendAddr pins s h v i))
          (s := 80*(w+1)) (fun _ => eqPort_size _ _)
        simp only [stepExpr, h, dite_true, Expr.size]
        omega
      · simp only [stepExpr, dite_eq_right h, Expr.size]
        omega
  have card : Fintype.card (Live w) = 14*w+1 := by
    simp only [Live, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
    omega
  have h := frame.withInput.step_size_le (stepExpr pins s v) _ hb
  rw [card, Frame.withInput_size] at h
  exact h

noncomputable def run (pins : StagePins w d σ) (v : Fin (2^d)) :
    List (Stage (1+d)) → Frame σ (Live w) → Frame σ (Live w)
  | [], f => f
  | s :: ss, f => run pins v ss (advance f pins s v)

def states (send : StageData w d) (v : Fin (2^d)) :
    List (Stage (1+d)) → (Fin 2 → Narrow w) → (Fin 2 → Narrow w)
  | [], cur => cur
  | s :: ss, cur => states send v ss (next s v (send s) cur)

def outgoingChecks (send : StageData w d) (v : Fin (2^d)) :
    List (Stage (1+d)) → (Fin 2 → Narrow w) → Prop
  | [], _ => True
  | s :: ss, cur => (∀ h, send s h v = cur) ∧ outgoingChecks send v ss (next s v (send s) cur)

theorem run_eval (hw : 2 ≤ w) (pins : StagePins w d σ) (send : StageData w d)
    (v : Fin (2^d)) (x : σ → Bool)
    (hs : ∀ s h u, u = v ∨ u = sourceSite s h v → ∀ i, ReadSlot hw x (pins s h u i) (send s h u i))
    (ss : List (Stage (1+d))) (frame : Frame σ (Live w)) (cur : Fin 2 → Narrow w)
    (hc : ReadLive hw (frame.eval x) cur) :
    ReadLive hw ((run pins v ss frame).eval x) (states send v ss cur) ∧
    (((run pins v ss frame).eval x (.inr ()) = true) ↔
       frame.eval x (.inr ()) = true ∧ outgoingChecks send v ss cur) := by
  induction ss generalizing frame cur with
  | nil => simp [run, states, outgoingChecks, hc]
  | cons s ss ih =>
    obtain ⟨hc', ht⟩ := advance_eval hw frame pins send s v x cur hc (hs s)
    obtain ⟨h₁, h₂⟩ := ih _ _ hc'
    exact ⟨h₁, by simpa only [run, outgoingChecks, ht, and_assoc] using h₂⟩

theorem run_size (pins : StagePins w d σ) (v : Fin (2^d)) (ss : List (Stage (1+d)))
    (frame : Frame σ (Live w)) :
    (run pins v ss frame).size ≤ frame.size + ss.length*((14*w+1)*(500*(w+1))) := by
  induction ss generalizing frame with
  | nil => simp [run]
  | cons s ss ih =>
    have ht := advance_size frame pins s v
    have h := ih (advance frame pins s v)
    rw [List.length_cons, Nat.succ_mul]
    exact h.trans (by omega)

end ThreeFlat.Diagonal.TraceSortSite

end OAI
