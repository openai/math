import OAI.Computability.NearSquareRoot.Specification
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Timely approximate multiplication on a fixed multitape machine -/

namespace OAI.Computability.MultitapeWeakETH

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
  disjointInputs : ∀ n (i j : Fin n), leftTape ≠ rightTape ∨ leftStart n + i.val ≠ rightStart n + j.val

noncomputable def InputLayout.load {A Q I : Type} (layout : InputLayout A Q I)
    (bit : Bool → A) {n : ℕ} (x y : Word n) : TM.Config A Q I := by
  classical
  let base := layout.background n
  exact ⟨base.pc,fun tape => ⟨(base.tape tape).pos, fun offset =>
    let cell := (base.tape tape).pos + offset
    let ix := cell - layout.leftStart n
    let iy := cell - layout.rightStart n
    if hx : tape = layout.leftTape ∧ 0 ≤ ix ∧ ix.toNat < n then bit (x ⟨ix.toNat,hx.2.2⟩)
    else if hy : tape = layout.rightTape ∧ 0 ≤ iy ∧ iy.toNat < n then bit (y ⟨iy.toNat,hy.2.2⟩)
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
  | none => NearSquareRoot.initialConfig M.start M.input M.bit M.sep M.blank (List.ofFn x) (List.ofFn y)
  | some layout => layout.load M.bit x y

/-- Execute a prefix of choices. A further transition from an already halted run fails. -/
def run (M : Machine) (coins : ℕ → M.Choice) (init : Config M) : ℕ → Option (Config M)
  | 0 => some init
  | t + 1 => (run M coins init t).bind (TM.advance (M.rule (coins t)))

def writes (M : Machine) {n : ℕ} (cfg : Config M) (out : Word n) : Prop :=
  ∀ i, (cfg.tape M.output).absolute (M.offset n + i.val) = M.bit (out i)

def timely (M : Machine) {n : ℕ} (T : ℕ) (seed : Fin (T+1) → M.Choice)
    (x y out : Word n) : Prop := ∃ t, ∃ ht : t ≤ T, ∃ cfg,
  run M (fun j => seed ⟨min j T, Nat.lt_succ_of_le (min_le_right ..)⟩) (initial M x y) t =
    some cfg ∧ TM.advance (M.rule (seed ⟨t, Nat.lt_succ_of_le ht⟩)) cfg = none ∧
    M.accepts cfg.pc = true ∧ writes M cfg out

noncomputable def density {n : ℕ} (event : Word n → Word n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun xy : Word n × Word n => event xy.1 xy.2).card : ℝ) /
    Fintype.card (Word n × Word n)

noncomputable def accurateDensity (M : Machine) (n T : ℕ) (seed : Fin (T+1) → M.Choice) :=
  density fun x y : Word n => ∃ out, timely M T seed x y out ∧
    100 * errors out (lowProduct x y) ≤ n

/-- A distribution on private transition schedules, sampled independently of
the input pair. At each time the selected rule still sees only the local view. -/
structure CoinLaw (M : Machine) (T : ℕ) where
  mass : (Fin (T+1) → M.Choice) → ℝ
  nonneg : ∀ seed, 0 ≤ mass seed
  total : ∑ seed, mass seed = 1

/-- Fresh coins may use a different distribution at each time. -/
noncomputable def CoinLaw.independent (M : Machine) (T : ℕ) (p : Fin (T+1) → M.Choice → ℝ)
    (nonneg : ∀ t c, 0 ≤ p t c) (total : ∀ t, ∑ c, p t c = 1) : CoinLaw M T where
  mass seed := ∏ t, p t (seed t)
  nonneg seed := Finset.prod_nonneg fun t _ => nonneg t (seed t)
  total := by rw [← Fintype.prod_sum]; simp [total]

noncomputable def success (M : Machine) (n T : ℕ) (law : CoinLaw M T) : ℝ :=
  ∑ seed, law.mass seed * accurateDensity M n T seed

theorem fix_private_coins (M : Machine) (n T : ℕ) (law : CoinLaw M T) :
    ∃ seed, success M n T law ≤ accurateDensity M n T seed := by
  classical
  obtain ⟨seed, _, hmax⟩ := Finset.exists_max_image Finset.univ (accurateDensity M n T)
    Finset.univ_nonempty
  refine ⟨seed, ?_⟩
  calc
    _ ≤ ∑ s, law.mass s * accurateDensity M n T seed :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hmax s (Finset.mem_univ _))
        (law.nonneg s)
    _ = _ := by rw [← Finset.sum_mul, law.total, one_mul]

def Sound (M : Machine) : Prop := ∀ n T seed (x y out : Word n),
  timely M T seed x y out → out = lowProduct x y

noncomputable def nondetDensity (M : Machine) (n T : ℕ) : ℝ :=
  density fun x y : Word n => ∃ seed out, timely M T seed x y out

noncomputable def threshold (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) / 100)

noncomputable def scale (n : ℕ) : ℝ := n * Real.sqrt (Real.logb 2 n)

def LowerBound (event : ℕ → ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T, event n T → c * scale n ≤ T

def MainStatement : Prop := ∀ M : Machine,
  LowerBound (fun n T => ∃ law, threshold n ≤ success M n T law) ∧
  (Sound M → LowerBound (fun n T => threshold n ≤ nondetDensity M n T))

end OAI.Computability.MultitapeWeakETH
