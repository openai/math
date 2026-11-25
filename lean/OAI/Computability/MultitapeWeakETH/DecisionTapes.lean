import OAI.Computability.MultitapeWeakETH.Price
import OAI.Computability.IntegerMultiplication.TMModel

/-! # Exact clock transfer from absolute-position tapes to the Weak ETH machine

The two libraries use a different representation of a bi-infinite tape.
The scanner's relative view and the mathlib tape agree at every integer
offset. This relation needs no space bound or slack in the running time.
-/

namespace OAI.Computability.MultitapeWeakETH.DecisionTapes

open DepthThreeLowerBound IntegerMultiplication Turing

variable {A Q I : Type} [Inhabited A]

def move : TM.Move → HeadMove
  | .left => .left
  | .stay => .stay
  | .right => .right

def code (rule : TM.Rule A Q I) : MultiTapeCode I A Q :=
  fun q r => (rule q r).map fun (p,ops) => (p,fun i => (ops i).1,fun i => move (ops i).2)

def Agrees (x : TM.Config A Q I) (y : MultiTapeCfg I A Q) :=
  x.pc = y.q ∧ ∀ k i, (x.tape k).view i = (y.tapes k).nth i

private theorem update {x : TM.Tape A} {y : Tape A} (eq : ∀ i, x.view i = y.nth i)
    (op : A × TM.Move) (i : ℤ) :
    (x.apply op).view i = ((move op.2).apply (y.write op.1)).nth i := by
  obtain ⟨w,m⟩ := op
  cases m <;> simp [TM.Tape.apply,TM.Move.shift,move,eq,sub_eq_add_neg]

theorem trace (rule : TM.Rule A Q I) {x z : TM.Config A Q I} {n : ℕ}
    (run : Trace (TM.advance rule) x n z) {y : MultiTapeCfg I A Q} (eq : Agrees x y) :
    ∃ w, runSteps (multiTapeStep (code rule)) n (some y) = some w ∧ Agrees z w := by
  induction run generalizing y with
  | nil => exact ⟨_,rfl,eq⟩
  | @cons x next z n step _ ih =>
    have reads : (fun i => (x.tape i).view 0) = fun i => (y.tapes i).head :=
      funext fun i => eq.2 i 0
    obtain ⟨⟨q,ops⟩,ruleAt,hnext⟩ := Option.map_eq_some_iff.mp step
    subst next
    have step' : multiTapeStep (code rule) y =
        some (multiTapeUpdate y q (fun i => (ops i).1) (fun i => move (ops i).2)) := by
      apply multiTapeStep_eq_some
      simp only [code,← eq.1,← reads,ruleAt,Option.map_some]
    obtain ⟨w,run,agrees⟩ := ih (y := multiTapeUpdate y q _ _)
      ⟨rfl,fun k i => update (eq.2 k) (ops k) i⟩
    refine ⟨w,?_,agrees⟩
    rw [Nat.add_comm,runSteps_succ_left,Option.bind_some,step']
    exact run

def start [DecidableEq I] (input : I) (symbol : Bool → A) (q : Q) (xs : List Bool) :
    TM.Config A Q I := ⟨q, fun i => TM.Tape.loaded default (if i = input then xs.map symbol else [])⟩

private theorem loaded (xs : List A) (i : ℤ) :
    (TM.Tape.loaded default xs).view i = (Tape.mk₁ xs).nth i := by
  cases i with
  | ofNat n =>
    change xs[n]?.getD default = (Tape.mk' (ListBlank.mk []) (ListBlank.mk xs)).nth (n:ℤ)
    simp [List.getI_eq_getElem?_getD]
  | negSucc n =>
    change default = (ListBlank.mk ([] : List A)).nth n
    simp

def machine [Fintype A] [Fintype I] [DecidableEq I] [Fintype Q] (rule : TM.Rule A Q I)
    (input : I) (symbol : Bool → A) (hinj : Function.Injective symbol) (mark : ∀ b, symbol b ≠ default)
    (q : Q) (accept : Q → Bool) : FiniteMultiTapeMachine where
  K := I
  Γ := A
  alphabetInhabited := inferInstanceAs (Inhabited A)
  tapeDecidableEq := inferInstanceAs (DecidableEq I)
  Q := Q
  inputTape := input
  inputSymbol := symbol
  input_injective := hinj
  input_ne_blank := mark
  initialState := q
  accept := accept
  code := code rule

theorem haltsIn [Fintype A] [Fintype I] [DecidableEq I] [Fintype Q] (rule : TM.Rule A Q I)
    (input : I) (symbol : Bool → A) (hinj : Function.Injective symbol) (mark : ∀ b, symbol b ≠ default)
    (q : Q) (accept : Q → Bool) (xs : List Bool) {z : TM.Config A Q I} {n : ℕ}
    (run : Trace (TM.advance rule) (start input symbol q xs) n z) (halt : TM.advance rule z = none) :
    MultiTapeHaltsIn (machine rule input symbol hinj mark q accept) xs (accept z.pc) n := by
  let M := machine rule input symbol hinj mark q accept
  have init : Agrees (start input symbol q xs) (M.init xs) := by
    refine ⟨rfl,?_⟩
    intro i j
    change (TM.Tape.loaded default (if i = input then xs.map symbol else [])).view j =
      (if i = input then Tape.mk₁ (xs.map symbol) else Tape.mk₁ []).nth j
    split <;> apply loaded
  obtain ⟨w,hw,eq⟩ := trace rule run init
  refine ⟨n,le_rfl,w,hw,?_,congrArg accept eq.1.symm⟩
  apply (multiTapeStep_eq_none_iff (code rule) w).mpr
  have hh := Option.map_eq_none_iff.mp halt
  have reads : (fun i => (z.tape i).view 0) = fun i => (w.tapes i).head := funext fun i => eq.2 i 0
  change (rule w.q _).map _ = none
  rw [← eq.1,← reads,hh]; rfl

end OAI.Computability.MultitapeWeakETH.DecisionTapes
