import OAI.Computability.VPVNP.SliceArithmeticRound

/-!
# Vector addition on serialized coefficient streams

A marker-controlled loop consumes the two vectors in increasing degree
order. Each iteration loads two limbs, adds modulo the supplied modulus,
and emits the sum. One final reversal puts the coefficient vector into the
first input port, with the original order of limbs and bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticAdd

open BurstRAM RAMTape SliceArithmetic SliceArithmeticStreamRow
open SliceArithmeticRound (packed)

variable {p w : ℕ} {X : Type} [DecidableEq X]

private def body (op : Word.Op) : FiniteRoutine (Port X) :=
  (((loadLimb .coeff 3).followedBy (loadLimb .factor 5)).followedBy
    ((Word.routine op 6 3 5 0).onPorts Sum.inl)).followedBy emit

/-- Apply the chosen residue operation once per degree marker, then reverse the emitted limbs
onto the coefficient stack. -/
def vectorOp (op : Word.Op) (marker : X) : FiniteRoutine (Port X) :=
  (FiniteRoutine.repeatMarked (.inr (.outer marker)) (body op)).followedBy
    (EvaluatorRadixDivision.reverseOnto (.inr .out) (.inr .coeff))

/-- The two input ports retain their suffixes. The caller supplies a scratch
port, an output port and a marker port for the duration of the call. -/
def streams (marker : X) (base : Stacks (StreamPort X))
    (coeff factor out : List Bool) (rows : ℕ) : Stacks (StreamPort X)
  | .coeff => coeff ++ base .coeff
  | .factor => factor ++ base .factor
  | .out => out
  | .scratch => []
  | .outer i => if i = marker then List.replicate rows true else base (.outer i)
  | i => base i

variable [NeZero p]

private def regs (op : Word.Op) (reg : Fin 8 → BurstRAM.Word w) (a b : Fin p) :=
  Function.update (Function.update (Function.update reg 3 (Word.limb w a)) 5 (Word.limb w b)) 6
    (Word.limb w (op.eval a b))

/-- Registers outside the two operand slots and the result slot are preserved. -/
def Preserves (reg next : Fin 8 → BurstRAM.Word w) :=
  ∀ i, i ≠ 3 → i ≠ 5 → i ≠ 6 → next i = reg i

private theorem body_runs (op : Word.Op) (hw : Word.workingWidth p ≤ w) (reg : Fin 8 → BurstRAM.Word w)
    (hp : (reg 0).val = p) (u : Stacks (StreamPort X)) (a b : Fin p) (as bs : List Bool)
    (ha : u .coeff = wordBits (Word.limb w a) ++ as) (hb : u .factor = wordBits (Word.limb w b) ++ bs)
    (ht : u .scratch = []) :
    let u' := Function.update (Function.update (Function.update u .coeff as) .factor bs) .out
      ((wordBits (Word.limb w (op.eval a b))).reverse ++ u .out)
    ∃ t ≤ 200 * (w + 1) ^ 2 + 17 * w + 7, (body op).Runs t (state reg u) (state (regs op reg a b) u') := by
  intro u'
  let r₁ := Function.update reg 3 (Word.limb w a)
  let s₁ := Function.update u .coeff as
  let r₂ := Function.update r₁ 5 (Word.limb w b)
  let s₂ := Function.update s₁ .factor bs
  have h₁ := loadLimb_runs (by simp) 3 reg u (Word.limb w a) as ha ht
  have h₂ := loadLimb_runs (s := .factor) (by simp) 5 r₁ s₁ (Word.limb w b) bs
    (by simpa [s₁] using hb) (by simpa [s₁] using ht)
  obtain ⟨t, ht', h₃⟩ := Word.routine_runs hw op 6 3 5 0 (by decide) Fin.elim0 0 r₂ [] a b
    (by simp [r₂, r₁, Word.limb_val hw]) (by simp [r₂, Word.limb_val hw]) (by simpa [r₂, r₁] using hp)
  have h₄ := emit_runs (regs op reg a b) s₂ (by simpa [s₂, s₁] using ht)
  have he : Function.update s₂ .out ((wordBits (regs op reg a b 6)).reverse ++ s₂ .out) = u' := by
    simp [regs, u', s₂, s₁]
  rw [he] at h₄
  exact ⟨_, by omega, ((h₁.followedBy h₂).followedBy (bankRun _ s₂ h₃)).followedBy h₄⟩

private def frame (marker : X) (base : Stacks (StreamPort X)) (reg : Fin 8 → BurstRAM.Word w)
    (xs : List (Fin p × Fin p)) (out : List Bool) : Stacks (Port X) :=
  state reg (streams marker base (packed w (xs.map Prod.fst)) (packed w (xs.map Prod.snd)) out xs.length)

private theorem scan_runs (op : Word.Op) (hw : Word.workingWidth p ≤ w) (marker : X) (base : Stacks (StreamPort X))
    (reg : Fin 8 → BurstRAM.Word w) (hp : (reg 0).val = p) (xs : List (Fin p × Fin p)) (out : List Bool) :
    ∃ (t : ℕ) (next : Fin 8 → BurstRAM.Word w), t ≤ xs.length * (200 * (w + 1) ^ 2 + 17 * w + 8) + 1 ∧
      Preserves reg next ∧ (FiniteRoutine.repeatMarked (.inr (.outer marker)) (body op)).Runs t
      (frame marker base reg xs out)
      (frame marker base next ([] : List (Fin p × Fin p)) ((packed w (xs.map (fun x => op.eval x.1 x.2))).reverse ++ out)) := by
  induction xs generalizing reg out with
  | nil =>
    refine ⟨1, reg, by simp, fun _ _ _ _ => rfl, ?_⟩
    simp only [List.map_nil, packed, List.flatMap_nil, List.reverse_nil, List.nil_append]
    apply Routine.Runs.popLoop_empty (.inr (.outer marker)) (fun _ => true) (Routine.halt false) (body op).body
    simp [frame, state, streams]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    let current := streams marker base (packed w (((a, b) :: xs).map Prod.fst))
      (packed w (((a, b) :: xs).map Prod.snd)) out (xs.length + 1)
    let u := Function.update current (.outer marker) (List.replicate xs.length true)
    let remaining := streams marker base (packed w (xs.map Prod.fst)) (packed w (xs.map Prod.snd))
      ((wordBits (Word.limb w (op.eval a b))).reverse ++ out) xs.length
    obtain ⟨t, ht, step⟩ := body_runs op hw reg hp u a b (remaining .coeff) (remaining .factor)
      (by simp [u, current, remaining, packed, streams]) (by simp [u, current, remaining, packed, streams])
      (by simp [u, current, streams])
    have hs : Function.update (Function.update (Function.update u .coeff (remaining .coeff)) .factor
        (remaining .factor)) .out ((wordBits (Word.limb w (op.eval a b))).reverse ++ u .out) = remaining := by
      funext i
      cases i with
      | outer j => by_cases h : j = marker <;> simp [u, current, remaining, streams, h]
      | old | coeff | factor | out | scratch => simp [u, current, remaining, streams]
    rw [hs] at step
    have same : Preserves reg (regs op reg a b) := fun i h₃ h₅ h₆ => by simp [regs, h₃, h₅, h₆]
    have hreg := congrArg Fin.val (same 0 (by decide) (by decide) (by decide))
    obtain ⟨n, next, hn, hnext, tail⟩ := ih (regs op reg a b) (hreg.trans hp) ((wordBits (Word.limb w (op.eval a b))).reverse ++ out)
    refine ⟨1 + t + n, next, ?_, fun i h₃ h₅ h₆ => (hnext i h₃ h₅ h₆).trans (same i h₃ h₅ h₆), ?_⟩
    · rw [List.length_cons, Nat.succ_mul xs.length]
      omega
    · apply Routine.Runs.popLoop_true_continue (.inr (.outer marker)) (fun _ => true) (Routine.halt false) (body op).body
        (mid := state (regs op reg a b) remaining) (n := t) (m := n) (tail := List.replicate xs.length true)
      · simp [frame, state, streams, List.replicate_succ]
      · rfl
      · simpa only [frame, List.length_cons, current, updateStream, u, remaining] using step
      · change (Routine.popLoop (.inr (.outer marker)) (fun _ => true) (Routine.halt false) (body op).body).Runs n
          (state (regs op reg a b) remaining) _ at tail
        simpa only [List.map_cons, packed, List.flatMap_cons, List.reverse_append, List.append_assoc] using tail

/-- Run one chosen prime-field operation on every pair of corresponding limbs. -/
theorem vectorOp_runs (op : Word.Op) {e : ℕ} (hw : Word.workingWidth p ≤ w) (marker : X)
    (base : Stacks (StreamPort X)) (reg : Fin 8 → BurstRAM.Word w) (hp : (reg 0).val = p)
    (a b : Vector p e) :
    ∃ (t : ℕ) (next : Fin 8 → BurstRAM.Word w),
      t ≤ e * (200 * (w + 1) ^ 2 + 17 * w + 8) + 2 * (e * w) + 2 ∧ Preserves reg next ∧
      (vectorOp op marker).Runs t
        (state reg (streams marker base (packed w (List.ofFn a)) (packed w (List.ofFn b)) [] e))
        (state next (streams marker base (packed w (List.ofFn (fun i => op.eval (a i) (b i)))) [] [] 0)) := by
  let xs := List.ofFn fun i => (a i, b i)
  let result := packed w (List.ofFn (fun i => op.eval (a i) (b i)))
  obtain ⟨t, next, ht, hp', run⟩ := scan_runs op hw marker base reg hp xs []
  have hsums : xs.map (fun x => op.eval x.1 x.2) = List.ofFn (fun i => op.eval (a i) (b i)) := by
    rw [List.map_ofFn]; rfl
  simp only [frame, hsums, List.map_nil, packed, List.flatMap_nil, List.length_nil, List.append_nil,
    xs, List.map_ofFn, Function.comp_def, List.length_ofFn] at run
  let s := state next (streams marker base [] [] result.reverse 0)
  let u := state next (streams marker base result [] [] 0)
  have reverseRun := EvaluatorRadixDivision.reverseOnto_runs (src := .inr (.out : StreamPort X))
    (dst := Sum.inr (.coeff : StreamPort X)) (by simp) s u rfl (by simp [s, u, state, streams]) (by
      rintro (j | j) hs hd
      · rfl
      · cases j <;> simp_all [s, u, state, streams])
  have hlen : (s (.inr .out)).length = e * w := by
    simp [s, state, streams, result]
  rw [hlen] at reverseRun
  have hbound : t ≤ e * (200 * (w + 1) ^ 2 + 17 * w + 8) + 1 := by simpa [xs] using ht
  refine ⟨t + (2 * (e * w) + 1), next, by omega, hp', ?_⟩
  unfold vectorOp
  apply FiniteRoutine.Runs.followedBy (s := _) (t := s) run
  exact reverseRun

/-- Addition of two packed coefficient vectors. -/
def vectorAdd (marker : X) : FiniteRoutine (Port X) := vectorOp .add marker

/-- The coefficient vector returned by the fixed control is the exact vector
sum in the advised quotient. Both input suffixes survive the operation. -/
theorem vectorAdd_runs {e : ℕ} (hw : Word.workingWidth p ≤ w) (marker : X)
    (base : Stacks (StreamPort X)) (reg : Fin 8 → BurstRAM.Word w) (hp : (reg 0).val = p)
    (a b : Vector p e) :
    ∃ (t : ℕ) (next : Fin 8 → BurstRAM.Word w),
      t ≤ e * (200 * (w + 1) ^ 2 + 17 * w + 8) + 2 * (e * w) + 2 ∧ Preserves reg next ∧
      (vectorAdd marker).Runs t
        (state reg (streams marker base (packed w (List.ofFn a)) (packed w (List.ofFn b)) [] e))
        (state next (streams marker base (packed w (List.ofFn (add a b))) [] [] 0)) :=
  vectorOp_runs .add hw marker base reg hp a b

end SliceArithmeticAdd

end VPVNP
end Computability
end OAI
