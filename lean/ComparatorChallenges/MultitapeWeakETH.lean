import Mathlib

/-! # Multitape integer multiplication under Weak ETH

The only hypothesis excludes a deterministic power saving in the exponent
for 3-SAT measured by variable count, allowing polynomial input overhead.

For each fixed multiplication machine the Ω(n√log n) bound holds uniformly
over large lengths and all deadlines. The randomized event allows at most
n/100 errors in the low n bits on a run that halts and accepts by the
deadline. The nondeterministic event counts inputs with a timely accepting
output, assuming every accepting output is exact. Both events have threshold
2^(-n/100) for uniformly sampled inputs.

For deterministic full products the sharp logarithmic exponent is stated
as a greatest lower bound.
-/

namespace OAI.DepthThreeLowerBound

universe uS uK uGamma uQ

def runSteps {S : Type uS} (step : S → Option S) (n : ℕ) (c : Option S) : Option S :=
  (fun oc => oc.bind step)^[n] c

inductive HeadMove
  | left
  | stay
  | right

def HeadMove.apply {Γ : Type uGamma} [Inhabited Γ] : HeadMove → Turing.Tape Γ → Turing.Tape Γ
  | .left, t => t.move Turing.Dir.left
  | .stay, t => t
  | .right, t => t.move Turing.Dir.right

structure MultiTapeCfg (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) [Inhabited Γ] where
  q : Q
  tapes : K → Turing.Tape Γ

abbrev MultiTapeCode (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) :=
  Q → (K → Γ) → Option (Q × (K → Γ) × (K → HeadMove))

def multiTapeUpdate {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ]
    (c : MultiTapeCfg K Γ Q) (q : Q) (writes : K → Γ) (moves : K → HeadMove) :
    MultiTapeCfg K Γ Q :=
  ⟨q, fun k => (moves k).apply ((c.tapes k).write (writes k))⟩

def multiTapeStep {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ]
    (code : MultiTapeCode K Γ Q) (c : MultiTapeCfg K Γ Q) : Option (MultiTapeCfg K Γ Q) :=
  (code c.q (fun k => (c.tapes k).head)).map fun out =>
    multiTapeUpdate c out.1 out.2.1 out.2.2

structure FiniteMultiTapeMachine where
  K : Type
  [tapeFinite : Fintype K]
  [tapeDecidableEq : DecidableEq K]
  inputTape : K
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Q : Type
  [stateFinite : Fintype Q]
  initialState : Q
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  code : MultiTapeCode K Γ Q
  accept : Q → Bool

attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

namespace FiniteMultiTapeMachine

abbrev Cfg (M : FiniteMultiTapeMachine) := MultiTapeCfg M.K M.Γ M.Q

abbrev step (M : FiniteMultiTapeMachine) : M.Cfg → Option M.Cfg :=
  multiTapeStep M.code

def init (M : FiniteMultiTapeMachine) (input : List Bool) : M.Cfg :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol)
    else Turing.Tape.mk₁ []⟩

end FiniteMultiTapeMachine

def MultiTapeHaltsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : M.Cfg,
    runSteps M.step k (some (M.init input)) = some c ∧
    M.step c = none ∧ M.accept c.q = output

end OAI.DepthThreeLowerBound

namespace OAI.Algorithms.SubexponentialSAT.SAT

universe u

abbrev Assignment (V : Type u) := V → Bool

structure Literal (V : Type u) where
  «variable» : V
  positive : Bool
  deriving DecidableEq

abbrev Clause (V : Type u) := Finset (Literal V)
abbrev CNF (V : Type u) := Finset (Clause V)

variable {V : Type u}

def Literal.eval (a : Assignment V) (l : Literal V) : Bool :=
  a l.variable == l.positive

variable [DecidableEq V]

def Clause.eval (a : Assignment V) (C : Clause V) : Bool :=
  decide (∃ l ∈ C, l.eval a = true)

def CNF.eval (a : Assignment V) (F : CNF V) : Bool :=
  decide (∀ C ∈ F, C.eval a = true)

def Satisfiable (F : CNF V) : Prop := ∃ a : Assignment V, F.eval a = true

def WidthAtMost (k : ℕ) (F : CNF V) : Prop := ∀ C ∈ F, C.card ≤ k

end OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms.SubexponentialSAT.Encoding

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def frame (bits : List Bool) : List Bool :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

def encodeList {α : Type*} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (frame (enc a) ++ encodeList enc as)

def literalCode {n : ℕ} (l : SAT.Literal (Fin n)) : ℕ :=
  2 * l.variable.val + if l.positive then 1 else 0

def clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) : List ℕ :=
  (C.image literalCode).sort (· ≤ ·)

def cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) : List (List ℕ) :=
  (F.image clauseNumbers).sort (· ≤ ·)

def encodeCNFBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeList (encodeList encodeNat) (cnfNumbers F)

def encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeNat n ++ encodeCNFBody F

end OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Computability

namespace MultitapeWeakETH

open OAI.DepthThreeLowerBound OAI.Algorithms.SubexponentialSAT

def PowerSavingDecision (answer : ∀ v, SAT.CNF (Fin v) → Bool) : Prop :=
  ∃ (η : ℝ) (C d : ℕ) (M : FiniteMultiTapeMachine), 0 < η ∧ η < 1 ∧
    ∀ v (formula : SAT.CNF (Fin v)), SAT.WidthAtMost 3 formula →
      ∃ t : ℕ, MultiTapeHaltsIn M (Encoding.encodeCNF formula) (answer v formula) t ∧
        (t : ℝ) ≤ (2 : ℝ) ^ (C * (v : ℝ) ^ (1 - η)) *
          (1 + v + (Encoding.encodeCNF formula).length : ℕ) ^ d

noncomputable def satAnswer (v : ℕ) (formula : SAT.CNF (Fin v)) : Bool := by
  classical exact decide (SAT.Satisfiable formula)

def WeakETH : Prop := ¬ PowerSavingDecision satAnswer

end MultitapeWeakETH

namespace IntegerMultiplication

/-- Exact n steps of a partial deterministic machine before consulting the next step. -/
inductive Trace {X : Type*} (step : X → Option X) : X → ℕ → X → Prop
  | nil (x) : Trace step x 0 x
  | cons {x y z n} : step x = some y → Trace step y n z → Trace step x (1 + n) z

namespace TM

inductive Move
  | left
  | stay
  | right

namespace Move
def shift : Move → ℤ
  | left => -1
  | stay => 0
  | right => 1
end Move

/-- On a tape seen relative to its head, position i is `pos + i` in absolute coordinates. -/
structure Tape (A : Type*) where
  pos : ℤ
  view : ℤ → A

namespace Tape
variable {A : Type*}

/-- Compute write followed by a move. -/
def apply (op : A × Move) (T : Tape A) : Tape A :=
  ⟨T.pos + op.2.shift,
    fun i => if i + op.2.shift = 0 then op.1 else T.view (i + op.2.shift)⟩

def absolute (T : Tape A) (i : ℤ) : A := T.view (i - T.pos)

def loaded (blank : A) (s : List A) : Tape A :=
  ⟨0, fun i => match i with
    | .ofNat n => s[n]?.getD blank
    | .negSucc _ => blank⟩

end Tape

variable {A Q I : Type}

structure Config (A Q I : Type) where
  pc : Q
  tape : I → Tape A

abbrev Rule (A Q I : Type) := Q → (I → A) → Option (Q × (I → A × Move))

def advance (m : Rule A Q I) (x : Config A Q I) : Option (Config A Q I) :=
  (m x.pc (fun i => (x.tape i).view 0)).map fun (q, o) =>
    ⟨q, fun i => (x.tape i).apply (o i)⟩

/-- Absolute tape contents after writing exactly s and otherwise blank (independent of
current head position). -/
def whole (blank : A) (s : List A) (T : Tape A) : Prop :=
  T.absolute = (Tape.loaded blank s).absolute

end TM

def bitValue (s : List Bool) : ℕ := s.foldl (fun v b => 2 * v + b.toNat) 0

end IntegerMultiplication

namespace NearSquareRoot

open IntegerMultiplication

noncomputable def initialConfig {A Q I : Type} (start : Q) (inp : I) (bit : Bool → A)
    (sep blank : A) (x y : List Bool) : TM.Config A Q I := by
  classical
  exact ⟨start, fun i => TM.Tape.loaded blank
    (if i = inp then x.map bit ++ [sep] ++ y.map bit else [])⟩

noncomputable def logScale (n : ℕ) : ℝ := 1 + Real.log n

end NearSquareRoot

namespace MultitapeWeakETH

open IntegerMultiplication

abbrev Word (n : ℕ) := Fin n → Bool

/-- Words on the physical input and output tapes are most significant bit first. -/
def lowProduct {n : ℕ} (x y : Word n) : Word n := fun index =>
  (bitValue (List.ofFn x) * bitValue (List.ofFn y)).testBit (n - 1 - index.val)

def errors {n : ℕ} (x y : Word n) : ℕ := (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- Input-independent initial contents, control and head positions, with two
prescribed nonoverlapping intervals of input cells. -/
structure InputLayout (A Q I : Type) where
  background : ℕ → TM.Config A Q I
  leftTape : I
  rightTape : I
  leftStart : ℕ → ℤ
  rightStart : ℕ → ℤ
  disjointInputs : ∀ n (i j : Fin n),
    leftTape ≠ rightTape ∨ leftStart n + i.val ≠ rightStart n + j.val

noncomputable def InputLayout.load {A Q I : Type} (layout : InputLayout A Q I)
    (bit : Bool → A) {n : ℕ} (x y : Word n) : TM.Config A Q I := by
  classical
  let base := layout.background n
  exact ⟨base.pc, fun tape => ⟨(base.tape tape).pos, fun offset =>
    let cell := (base.tape tape).pos + offset
    let ix := cell - layout.leftStart n
    let iy := cell - layout.rightStart n
    if hx : tape = layout.leftTape ∧ 0 ≤ ix ∧ ix.toNat < n then bit (x ⟨ix.toNat, hx.2.2⟩)
    else if hy : tape = layout.rightTape ∧ 0 ≤ iy ∧ iy.toNat < n then bit (y ⟨iy.toNat, hy.2.2⟩)
    else (base.tape tape).view offset⟩⟩

/-- Each choice selects a local transition on the symbols under the heads. The
output interval can depend on length, for example the suffix of a full product. -/
structure Machine where
  Alphabet : Type
  State : Type
  Tapes : Type
  Choice : Type
  [alphabetFinite : Finite Alphabet]
  [stateFinite : Finite State]
  [tapesFinite : Finite Tapes]
  [choiceFintype : Fintype Choice]
  [choiceNonempty : Nonempty Choice]
  bit : Bool → Alphabet
  bit_injective : Function.Injective bit
  sep : Alphabet
  blank : Alphabet
  markers : ∀ b, bit b ≠ sep ∧ bit b ≠ blank
  sep_ne_blank : sep ≠ blank
  input : Tapes
  output : Tapes
  offset : ℕ → ℤ
  start : State
  rule : Choice → TM.Rule Alphabet State Tapes
  accepts : State → Bool
  layout : Option (InputLayout Alphabet State Tapes) := none

attribute [instance] Machine.choiceFintype Machine.choiceNonempty

abbrev Config (M : Machine) := TM.Config M.Alphabet M.State M.Tapes

noncomputable def initial (M : Machine) {n : ℕ} (x y : Word n) : Config M :=
  match M.layout with
  | none =>
    NearSquareRoot.initialConfig M.start M.input M.bit M.sep M.blank (List.ofFn x) (List.ofFn y)
  | some layout => layout.load M.bit x y

/-- Execute a prefix of choices. A further transition from an already halted run fails. -/
def run (M : Machine) (coins : ℕ → M.Choice) (init : Config M) : ℕ → Option (Config M)
  | 0 => some init
  | t + 1 => (run M coins init t).bind (TM.advance (M.rule (coins t)))

def writes (M : Machine) {n : ℕ} (cfg : Config M) (out : Word n) : Prop :=
  ∀ i, (cfg.tape M.output).absolute (M.offset n + i.val) = M.bit (out i)

def timely (M : Machine) {n : ℕ} (T : ℕ) (seed : Fin (T + 1) → M.Choice)
    (x y out : Word n) : Prop := ∃ t, ∃ ht : t ≤ T, ∃ cfg,
  run M (fun j => seed ⟨min j T, Nat.lt_succ_of_le (min_le_right ..)⟩) (initial M x y) t =
    some cfg ∧ TM.advance (M.rule (seed ⟨t, Nat.lt_succ_of_le ht⟩)) cfg = none ∧
    M.accepts cfg.pc = true ∧ writes M cfg out

noncomputable def density {n : ℕ} (event : Word n → Word n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun xy : Word n × Word n => event xy.1 xy.2).card : ℝ) /
    Fintype.card (Word n × Word n)

noncomputable def accurateDensity (M : Machine) (n T : ℕ) (seed : Fin (T + 1) → M.Choice) :=
  density fun x y : Word n => ∃ out, timely M T seed x y out ∧
    100 * errors out (lowProduct x y) ≤ n

/-- A distribution on private transition schedules, sampled independently of
the input pair. At each time the selected rule still sees only the local view. -/
structure CoinLaw (M : Machine) (T : ℕ) where
  mass : (Fin (T + 1) → M.Choice) → ℝ
  nonneg : ∀ seed, 0 ≤ mass seed
  total : ∑ seed, mass seed = 1

noncomputable def success (M : Machine) (n T : ℕ) (law : CoinLaw M T) : ℝ :=
  ∑ seed, law.mass seed * accurateDensity M n T seed

def Sound (M : Machine) : Prop := ∀ n T seed (x y out : Word n),
  timely M T seed x y out → out = lowProduct x y

noncomputable def nondetDensity (M : Machine) (n T : ℕ) : ℝ :=
  density fun x y : Word n => ∃ seed out, timely M T seed x y out

-- In the solution, the hypothesis and machine bounds live in different modules.
-- Start a fresh cache so the numeral proofs receive the same names here.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def threshold (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) / 100)

noncomputable def scale (n : ℕ) : ℝ := n * Real.sqrt (Real.logb 2 n)

def LowerBound (event : ℕ → ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T, event n T → c * scale n ≤ T

def MainStatement : Prop := ∀ M : Machine,
  LowerBound (fun n T => ∃ law, threshold n ≤ success M n T law) ∧
  (Sound M → LowerBound (fun n T => threshold n ≤ nondetDensity M n T))

theorem main_of_weakETH (weak : WeakETH) : MainStatement := by
  sorry

open NearSquareRoot Filter

/-- One fixed deterministic rule writes the full product within the clock at every positive width. -/
def ExactClock (W : ℕ → ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q) (rule : TM.Rule A Q I),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    ∀ n : ℕ, 0 < n → ∀ x y : Word n, ∃ t ≤ W n, ∃ cfg z,
      Trace (TM.advance rule) (initialConfig start inp bit sep blank (List.ofFn x) (List.ofFn y))
        t cfg ∧ TM.advance rule cfg = none ∧ TM.whole blank (z.map bit) (cfg.tape out) ∧
      z.length = 2 * n ∧ bitValue z = bitValue (List.ofFn x) * bitValue (List.ofFn y)

def Achievable (r : ℝ) : Prop := ∃ W : ℕ → ℕ, ExactClock W ∧ ∃ C : ℝ, 0 < C ∧
  ∀ᶠ n in atTop, (W n : ℝ) ≤ C * n * logScale n ^ r

theorem optimal_exponent_of_weakETH (weak : WeakETH) :
    IsGLB {r | Achievable r} (1 / 2 : ℝ) := by
  sorry

end MultitapeWeakETH
end OAI.Computability
