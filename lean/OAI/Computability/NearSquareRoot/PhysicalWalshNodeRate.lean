import OAI.Computability.NearSquareRoot.PhysicalWalshChargesOn
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeEntry
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeEnvelope

/-! # Time and visited cells for a recursive selected-bit Walsh piece

A raw compact descriptor and flat, marked record array enter the fixed piece
program. It computes the initial dispatch tag, executes the recursive kernel,
and returns the same compact descriptor with the transformed record array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code Space PhysicalWalsh KernelPass

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

abbrev Admitted := {v : Invocation hw p // withinWidth (a+1) v.shape}

def rawInput (v : Admitted hw p) : Tree := buffer (a+1) v.val.shape v.val.row

def rawOutput (v : Admitted hw p) : Tree := buffer (a+1) v.val.shape (run hw p v.val.shape v.val.row)

/-- The local program interface supplied by layout setup, the fixed template,
and its physical controlled-interchange instructions. -/
def Programs (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) : Prop :=
  let vm := spec hw p scan arena cost
  BoundedTask (fun x : vm.Base => scan x.val.shape) (fun x => arena x.val.shape)
      (fun x => vm.payload x.val) (fun x => vm.reply x.val) ∧
    OpenRun vm.meter p.calls (fun x : vm.Step => x.val.shape) (fun x => vm.payload x.val) (fun x => vm.reply x.val)

noncomputable def pieceTime (A W calls : ℕ) (ρ c : ℝ) (L P : ℕ → ℝ) (s : Shape) : ℕ :=
  charge W calls (localTime A ρ c (L s.w) (P s.w)) s.level (bitVolume A s)

noncomputable def pieceSpace (A W : ℕ) (c : ℝ) (P : ℕ → ℝ) (s : Shape) : ℕ :=
  charge W 1 (localSpace c (P s.w)) s.level (bitVolume A s)

private theorem local_le_charge (W calls : ℕ) (f : ℕ → ℝ → ℝ) (j : ℕ) (V : ℝ) :
    ⌊f j V⌋₊ ≤ charge W calls f j V := by cases j <;> simp [PhysicalWalsh.charge]

/-- Execute an untagged request with the integral budgets of the analytic
recurrences. Inserting the dispatch tag itself fits in the root's allowance. -/
theorem rawPiece (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s)
    (prog : Programs hw p scan arena cost) (entry : ∀ s, withinWidth (a+1) s → allowance (a+1) 1 s ≤ arena s)
    (ρ c : ℝ) (L P : ℕ → ℝ) (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ L w)
    (ht : ∀ s, withinWidth (a+1) s → (scan s : ℝ)+1 ≤ localTime (a+1) ρ c (L s.w) (P s.w) s.level (bitVolume (a+1) s))
    (hs : ∀ s, withinWidth (a+1) s → (arena s : ℝ)+1 ≤ localSpace c (P s.w) s.level (bitVolume (a+1) s)) :
    BoundedTask (fun v : Admitted hw p => pieceTime (a+1) W p.calls ρ c L P v.val.shape)
      (fun v => pieceSpace (a+1) W c P v.val.shape) (rawInput hw p) (rawOutput hw p) := by
  let vm := spec hw p scan arena cost
  let layout := chargeLayout hw p scan arena cost
  have core := layout.boundedOn (withinWidth (a+1)) (fun edge h => withinWidth_child hw edge h) prog.1 prog.2
    (fun w => localTime (a+1) ρ c (L w) (P w)) (fun w => localSpace c (P w))
    (fun w => localTime_mono hc (hL w)) (fun _ => localSpace_mono hc) ht hs
  have tag := Header.entry_query hw p scan arena cost (fun v : Admitted hw p => v.val)
  apply (tag.compose core).bound 2 1 <;> intro v
  · have h : scan v.val.shape ≤ pieceTime (a+1) W p.calls ρ c L P v.val.shape :=
      (Nat.le_floor ((le_add_of_nonneg_right zero_le_one).trans (ht _ v.property))).trans (local_le_charge ..)
    have g := (entry _ v.property).trans ((cost _).trans h)
    change allowance (a+1) 1 v.val.shape + pieceTime (a+1) W p.calls ρ c L P v.val.shape + 1 ≤ _
    omega
  · have h : arena v.val.shape ≤ pieceSpace (a+1) W c P v.val.shape :=
      (Nat.le_floor ((le_add_of_nonneg_right zero_le_one).trans (hs _ v.property))).trans (local_le_charge ..)
    have g := (entry _ v.property).trans h
    change max (allowance (a+1) 1 v.val.shape) (pieceSpace (a+1) W c P v.val.shape) + 1 ≤ _
    simp [max_eq_right g]

/-- Closed time bound for one occupied even piece at any depth. -/
noncomputable def pieceTimeBound (A calls : ℕ) (ρ B : ℝ) (L P : ℕ → ℝ) (s : Shape) : ℕ :=
  ⌊B*L s.w*bitVolume A s*((2:ℝ)*(A:ℝ)^s.level)^ρ + P s.w*(calls+1:ℝ)^s.level⌋₊

/-- Closed peak bound, including all parent frames on the active path. -/
noncomputable def pieceSpaceBound (A : ℕ) (c : ℝ) (P : ℕ → ℝ) (s : Shape) : ℕ :=
  ⌊2*c*bitVolume A s+(s.level+1:ℝ)*P s.w⌋₊

theorem pieceTime_le {A W calls : ℕ} {ρ c : ℝ} (arity : 1 ≤ A) (width : 0 < W) (hr : 0 ≤ ρ) (hc : 0 ≤ c)
    (saving : (calls : ℝ)/W < (A:ℝ)^ρ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ L P : ℕ → ℝ,
    (∀ w, 0 ≤ L w) → (∀ w, 0 ≤ P w) → ∀ s : Shape,
    pieceTime A W calls ρ c L P s ≤ pieceTimeBound A calls ρ B L P s := by
  obtain ⟨B,hB,time⟩ := charge_time_bound arity width hr hc saving
  exact ⟨B,hB,fun L P hL hP s => Nat.le_floor <| time (L _) (P _) (hL _) (hP _) _ _ (bitVolume_nonneg A s)⟩

theorem pieceSpace_le {A W : ℕ} {c : ℝ} {P : ℕ → ℝ} (wide : 2 ≤ W) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    (s : Shape) : pieceSpace A W c P s ≤ pieceSpaceBound A c P s :=
  Nat.le_floor <| charge_space_bound wide hc (hP _) _ _ (bitVolume_nonneg A s)

/-- A fixed time coefficient works across all levels, inputs and widths.
The word-width polynomials in the additive term are kept pointwise. -/
theorem rawPieceRate {ρ c : ℝ} {L P : ℕ → ℝ} (wide : 2 ≤ W) (hr : 0 ≤ ρ) (hc : 0 ≤ c)
    (hL : ∀ w, 0 ≤ L w) (hP : ∀ w, 0 ≤ P w) (saving : (p.calls : ℝ)/W < ((a+1 : ℕ):ℝ)^ρ)
    (task : BoundedTask (fun v : Admitted hw p => pieceTime (a+1) W p.calls ρ c L P v.val.shape)
      (fun v => pieceSpace (a+1) W c P v.val.shape) (rawInput hw p) (rawOutput hw p)) :
    ∃ B : ℝ, 0 ≤ B ∧ BoundedTask (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L P v.val.shape)
      (fun v => pieceSpaceBound (a+1) c P v.val.shape) (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨B,hB,time⟩ := pieceTime_le (Nat.succ_le_succ (Nat.zero_le a)) hw hr hc saving
  exact ⟨B,hB,task.mono (fun v => time L P hL hP v.val.shape) (fun v => pieceSpace_le wide hc hP v.val.shape)⟩

/-- The width-polynomial area and the full output tape copy are included in
this physical clock. The output is the untagged descriptor and complete row. -/
theorem releasePiece {T S : Admitted hw p → ℕ} (task : BoundedTask T S (rawInput hw p) (rawOutput hw p))
    (entry : ∀ v, allowance (a+1) 1 v.val.shape ≤ T v) :
    ∃ C : ℕ, TapeRun (fun v => C*(T v+1)) (fun v => C*(S v+1)) (rawInput hw p) (rawOutput hw p) := by
  apply task.releaseWithin 10
  exact fun v => (Header.payload_size (a+1) v.val.shape _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (entry v)))

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
