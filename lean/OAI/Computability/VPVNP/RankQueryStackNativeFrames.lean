import OAI.Computability.VPVNP.RankQueryStackEngine
import OAI.Computability.VPVNP.SliceArithmeticRound

/-! # Physical Schur frame fields with native extension-field scalars

The query and loop registers use ordinary binary words. Accumulators and left
operands keep the low-degree-first stream of base-field limbs consumed by
the extension-field arithmetic. The direction takes one bit and the unused
left operand occupies an empty field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine

open RAMTape Evaluator.InputBank

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e} {K : Type}

/-- The ten bit-string fields of a live Schur frame or its corresponding ten history stacks. -/
abbrev Data := Fin 10 → List Bool
/-- A Schur query for an order-`n` matrix with coefficient degrees bounded by `U` and `Z`. -/
abbrev Key (n U Z : ℕ) := SchurKey n U Z
/-- A suspended Schur continuation whose accumulator and operands belong to the scalar ring
specified by `c`. -/
abbrev F (n U Z : ℕ) (c : SliceArithmetic.Vector p e) := Frame.SchurFrame n U Z c

/-- Encode a scalar as its low-degree-first list of base-field coefficients, each in a `v`-bit
limb. -/
def scalar (v : ℕ) (a : Scalar c) : List Bool := SliceArithmeticRound.packed v (List.ofFn a.digits)

@[simp] theorem scalar_length (v : ℕ) (a : Scalar c) : (scalar v a).length = e*v := by
  simp [scalar]

/-- Assemble the ten live fields from the direction tag, six query words, remaining count,
accumulator, and saved left factor. -/
def fields (w : ℕ) (tag : List Bool) (q : Key n U Z) (count acc left : List Bool) : Data :=
  Fin.cons tag (Fin.append (fun i => UniversalCountStack.digits w (q.words i)) ![count,acc,left])

/-- Encode a suspended continuation, saving the left scalar in a frame waiting for its right
child. -/
def nativeFrame (w v : ℕ) : F n U Z c → Data
  | .left q k a => fields w [false] q (UniversalCountStack.digits w k) (scalar v a) []
  | .right q k a l => fields w [true] q (UniversalCountStack.digits w k) (scalar v a) (scalar v l)

theorem frame_length (w v : ℕ) (f : F n U Z c) (i : Fin 10) :
    (nativeFrame w v f i).length ≤ max 1 (max w (e*v)) := by
  cases f with
  | left q k a =>
    refine Fin.cases (by simp [nativeFrame, fields]) (fun j => ?_) i
    refine Fin.addCases (motive := fun i => (Fin.append (fun x => UniversalCountStack.digits w (q.words x))
      ![UniversalCountStack.digits w k,scalar v a,[]] i).length ≤ _) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simp
    · rw [Fin.append_right]; fin_cases x <;> simp
  | right q k a l =>
    refine Fin.cases (by simp [nativeFrame, fields]) (fun j => ?_) i
    refine Fin.addCases (motive := fun i => (Fin.append (fun x => UniversalCountStack.digits w (q.words x))
      ![UniversalCountStack.digits w k,scalar v a,scalar v l] i).length ≤ _) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simp
    · rw [Fin.append_right]; fin_cases x <;> simp

/-- Encode a list of suspended frames into parallel history stacks, with the top frame's
delimited fields first. -/
def history (w v : ℕ) (fs : List (F n U Z c)) : Data :=
  fun i => fs.flatMap (fun f => fieldBits (nativeFrame w v f i))

theorem history_cons (w v : ℕ) (f : F n U Z c) (fs : List (F n U Z c)) :
    history w v (f :: fs) = fun i => fieldBits (nativeFrame w v f i) ++ history w v fs i := by
  funext i; simp [history]

theorem history_length_le (w v : ℕ) (fs : List (F n U Z c)) (i : Fin 10) :
    (history w v fs i).length ≤ fs.length * (2*max 1 (max w (e*v))+1) := by
  induction fs with
  | nil => simp [history]
  | cons f fs ih =>
    rw [history_cons, List.length_append, length_fieldBits, List.length_cons, Nat.add_mul, one_mul]
    have := frame_length w v f i
    omega

/-- The complete physical bank. The auxiliary port values depend on the
installed arithmetic routines and the persistent matrix description. -/
def store (live saved : Data) (signal result : List Bool) (aux : Stacks K) : Stacks (Port K)
  | .frame (.inl i) => live i
  | .frame (.inr i) => saved i
  | .condition => signal
  | .result => result
  | .aux i => aux i

private theorem cost_le (s : Data) (c b : ℕ) (h : ∀ i, (s i).length ≤ b) :
    (((List.finRange 10).map (fun i => 3*(s i).length+c)).sum+1) ≤ 10*(3*b+c)+1 := by
  have hl (xs : List (Fin 10)) : (xs.map (fun i => 3*(s i).length+c)).sum ≤ xs.length*(3*b+c) := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      have := h i
      omega
  simpa only [List.length_finRange] using Nat.add_le_add_right (hl (List.finRange 10)) 1

variable [DecidableEq K]

theorem save_runs (a : Actions K) (w v : ℕ) (f : F n U Z c) (fs : List (F n U Z c))
    (ret : List Bool) (aux : Stacks K) :
    ∃ t ≤ 10*(3*max 1 (max w (e*v))+2)+1,
      (a.callee .save).Runs t (store (nativeFrame w v f) (history w v fs) [] ret aux)
        (store (fun _ => []) (history w v (f :: fs)) [] ret aux) := by
  refine ⟨_, cost_le _ _ _ (frame_length w v f), ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ (ports := Port.frame) (fun _ _ h => Port.frame.inj h)
    (FrameStore.push_data_runs (nativeFrame w v f) (history w v fs))
  · intro k; cases k <;> rfl
  · intro k; cases k with
    | inl => rfl
    | inr i => exact congrFun (history_cons ..) i
  · intro l hl; cases l <;> first | rfl | exact (hl _ rfl).elim

theorem restore_runs (a : Actions K) (w v : ℕ) (f : F n U Z c) (fs : List (F n U Z c))
    (ret : List Bool) (aux : Stacks K) :
    ∃ t ≤ 10*(3*max 1 (max w (e*v))+1)+1,
      (a.callee .restore).Runs t (store (fun _ => []) (history w v (f :: fs)) [] ret aux)
        (store (nativeFrame w v f) (history w v fs) [] ret aux) := by
  refine ⟨_, cost_le _ _ _ (frame_length w v f), ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ (ports := Port.frame) (fun _ _ h => Port.frame.inj h)
    (FrameStore.pop_data_runs (nativeFrame w v f) (history w v fs))
  · intro k; cases k with
    | inl => rfl
    | inr i => exact congrFun (history_cons ..) i
  · intro k; cases k <;> rfl
  · intro l hl; cases l <;> first | rfl | exact (hl _ rfl).elim

end RankQuery.Stack.Engine

end VPVNP
end Computability
end OAI
