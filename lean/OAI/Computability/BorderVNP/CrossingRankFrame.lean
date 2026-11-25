import OAI.Computability.BorderVNP.CrossingRankAdder
import OAI.Computability.BorderVNP.CrossingStateIndex

/-!
# A polynomial-size Boolean verifier for the occupation-state code

A layer for the next occupied mode updates the rank and validity at every residual
budget. The precomputed selectedValue-or-exclude counts are circuit constants. The circuit
returns the full binary rank as well as the validity bit needed when intermediate
states are guessed instead of decoded.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.StateIndex

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open Lemmata.FockCircuits (doubledEnergy)

/-- One input bit per available mode. -/
def occupancy {E : ℕ} (x : Fin E → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin E => x i)).map Fin.valEmbedding

private def inputBit {E : ℕ} (x : Fin E → Bool) (i : ℕ) : Bool :=
  if hi : i < E then x ⟨i,hi⟩ else false

private def prefixMask {E : ℕ} (x : Fin E → Bool) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => inputBit x i)

private theorem prefix_succ {E : ℕ} (x : Fin E → Bool) (t : ℕ) :
    prefixMask x (t+1) = if inputBit x t then insert t (prefixMask x t) else prefixMask x t := by
  simp [prefixMask, Finset.range_add_one, Finset.filter_insert]

private theorem pivot_not_mem {E : ℕ} (x : Fin E → Bool) (t : ℕ) : t ∉ prefixMask x t := by
  simp [prefixMask]

private theorem prefix_full {E : ℕ} (x : Fin E → Bool) : prefixMask x E = occupancy x := by
  ext j
  simp only [prefixMask, occupancy, Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ,
    true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hj, hx⟩
    exact ⟨⟨j,hj⟩, by simpa [inputBit, hj] using hx, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, by simpa [inputBit] using hi⟩

private abbrev Wires (E : ℕ) := Fin E ⊕ Fin (2*E+1) × Option (Fin (E+1))

private def initialExpr (E : ℕ) : Wires E → Expr (Fin E)
  | .inl i => .input i
  | .inr (_, none) => .const true
  | .inr (_, some _) => .const false

private def targetBudget {E : ℕ} (t : ℕ) (b : Fin (2*E+1)) : Fin (2*E+1) :=
  ⟨b.val - (2*t+1), (Nat.sub_le ..).trans_lt b.isLt⟩

private def readBit {E : ℕ} (b : Fin (2*E+1)) (j : ℕ) : Expr (Wires E) :=
  if hj : j < E+1 then .input (.inr (b,some ⟨j,hj⟩)) else .const false

private def layer (E t : ℕ) : Wires E → Expr (Wires E)
  | .inl i => .input (.inl i)
  | .inr (b,j) => if ht : t < E then
      let chosen := Expr.input (.inl ⟨t,ht⟩)
      let selectedValue := match j with
        | none => if 2*t+1 ≤ b.val then .input (.inr (targetBudget t b, none)) else .const false
        | some bit => addConstBit (readBit (targetBudget t b)) (count t b.val) bit.val
      Expr.mux chosen selectedValue (.input (.inr (b,j)))
    else .input (.inr (b,j))

private noncomputable def scan (E t : ℕ) : Frame (Fin E) (Wires E) :=
  ((Frame.initial id).step (initialExpr E)).steps (layer E) t

private theorem scan_eval {E : ℕ} (x : Fin E → Bool) (t : ℕ) (ht : t ≤ E) :
    (∀ i, (scan E t).eval x (.inl i) = x i) ∧
      (∀ b, (scan E t).eval x (.inr (b,none)) = decide (doubledEnergy (prefixMask x t) ≤ b.val)) ∧
      ∀ b j, (scan E t).eval x (.inr (b,some j)) = (rank t b.val (prefixMask x t)).testBit j.val := by
  induction t with
  | zero => simp [scan, initialExpr, prefixMask, doubledEnergy, rank, Expr.eval]
  | succ t ih =>
    have hlt : t < E := by omega
    obtain ⟨hinput, hvalid, hbits⟩ := ih hlt.le
    have hstep : scan E (t+1) = (scan E t).step (layer E t) := rfl
    refine ⟨fun i => by simp [hstep, layer, Expr.eval, hinput], ?_, ?_⟩
    · intro b
      rw [hstep, Frame.step_eval, layer, dite_eq_left hlt, Expr.eval_mux, Expr.eval, hinput, prefix_succ]
      have absent := pivot_not_mem x t
      cases hx : x ⟨t,hlt⟩
      · simpa [inputBit, hlt, hx, Expr.eval] using hvalid b
      · simp only [inputBit, hlt, dite_eq_left, hx, ↓reduceIte]
        rw [show doubledEnergy (insert t (prefixMask x t)) = 2*t+1 + doubledEnergy (prefixMask x t) by
          simp [doubledEnergy, Finset.sum_insert absent]]
        by_cases hb : 2*t+1 ≤ b.val
        · simp only [hb, ite_true, Expr.eval, hvalid, targetBudget]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
        · simp [hb, Expr.eval]
          omega
    · intro b j
      rw [hstep, Frame.step_eval, layer, dite_eq_left hlt, Expr.eval_mux, Expr.eval, hinput, prefix_succ]
      have absent := pivot_not_mem x t
      cases hx : x ⟨t,hlt⟩
      · simpa [inputBit, hlt, hx, rank, absent, Expr.eval] using hbits b j
      · simp only [inputBit, hlt, dite_eq_left, hx, ↓reduceIte, rank, Finset.mem_insert_self,
          Finset.erase_insert absent]
        apply addConstBit_eval
        intro i hij
        have hi : i < E+1 := hij.trans_lt j.isLt
        simpa [readBit, hi, Expr.eval, targetBudget] using hbits (targetBudget t b) ⟨i,hi⟩

/-- The rank bits are little-endian. The additional high bit also tests as zero for every
admissible state since there are at most `2^E` possible masks. -/
noncomputable def rankFrame (E : ℕ) : Frame (Fin E) (Fin (E+1)) :=
  (scan E E).select (fun j => .inr (Fin.last (2*E), some j))

/-- The validity bit detects the energy constraint on guessed occupation masks. -/
noncomputable def validFrame (E : ℕ) : Frame (Fin E) Unit :=
  (scan E E).select (fun _ => .inr (Fin.last (2*E), none))

/-- Every binary rank bit agrees with the canonical indexing from the state table. -/
theorem rankFrame_eval (E : ℕ) (x : Fin E → Bool) (j : Fin (E+1)) :
    (rankFrame E).eval x j = (rank E (2*E) (occupancy x)).testBit j.val := by
  simpa [rankFrame, prefix_full] using (scan_eval x E le_rfl).2.2 (Fin.last (2*E)) j

/-- A guessed mask is accepted exactly when its doubled energy fits the cutoff. -/
theorem validFrame_eval (E : ℕ) (x : Fin E → Bool) :
    (validFrame E).eval x () = decide (doubledEnergy (occupancy x) ≤ 2*E) := by
  simpa [validFrame, prefix_full] using (scan_eval x E le_rfl).2.1 (Fin.last (2*E))

private theorem layer_size (E t : ℕ) (i : Wires E) : (layer E t i).size ≤ 4*E+17 := by
  rcases i with i | ⟨b, _ | j⟩
  · simp [layer, Expr.size]
  · by_cases ht : t < E <;> by_cases hb : 2*t+1 ≤ b.val <;> simp [layer, ht, hb, Expr.mux, Expr.size]
  · by_cases ht : t < E
    · have h := addConstBit_size (readBit (targetBudget t b)) (count t b.val) j.val
          (fun i => by by_cases hi : i < E+1 <;> simp [readBit, hi, Expr.size])
      simp [layer, ht, Expr.mux, Expr.size]
      omega
    · simp [layer, ht, Expr.size]

private theorem scan_size (E : ℕ) :
    (scan E E).size ≤ (E+(2*E+1)*(E+2)) * (1+E*(4*E+17)) := by
  let L := Fintype.card (Wires E)
  have hL : L = E+(2*E+1)*(E+2) := by simp [L, Nat.add_assoc]
  have hi := Frame.step_size_le (Frame.initial (id : Fin E → Fin E)) (initialExpr E) 1
    (fun i => by rcases i with i | ⟨_, _ | _⟩ <;> simp [initialExpr, Expr.size])
  have h := Frame.steps_size_le ((Frame.initial id).step (initialExpr E)) (layer E) E (4*E+17)
    (fun t _ i => layer_size E t i)
  simp only [Frame.initial_size, zero_add, Nat.mul_one] at hi
  change (scan E E).size ≤ _ at h
  calc
    _ ≤ L + E * (L * (4*E+17)) := h.trans (Nat.add_le_add_right hi _)
    _ = _ := by rw [hL]; ring

/-- The rank circuit is polynomial in the largest mode. Its gate bound includes every
residual budget and all of the adder bits, without a table indexed by occupation masks. -/
theorem rankFrame_size (E : ℕ) :
    (rankFrame E).size ≤ (E+(2*E+1)*(E+2)) * (1+E*(4*E+17)) :=
  scan_size E

/-- The validity circuit is a selection from the same bounded gate array. -/
theorem validFrame_size (E : ℕ) :
    (validFrame E).size ≤ (E+(2*E+1)*(E+2)) * (1+E*(4*E+17)) :=
  scan_size E

end Crossing.StateIndex

end BorderVNP
end Computability
end OAI
