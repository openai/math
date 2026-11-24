import OAI.Computability.VPVNP.LiveEvaluatorStep
import OAI.Computability.VPVNP.RAMTapeSpaceNamed

/-!
# Window radius for the compiled evaluator

An absolute bound on both head positions bounds every tape write. The
nonblank support of the initial input is retained as well. Translating
these absolute positions to the current head yields a time-independent
window bound at every cut, including prefixes of malformed choice strings.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorSpace

open UniversalMachine LiveEvaluatorEncoding EvaluatorTail RAMTape RAMTape.StackCompiler

/-- All nonblank symbols lie in a fixed physical interval centered at the
initial head. `pos` is the position of the current head. -/
def SupportedAt (S : ℕ) (pos : ℤ) (t : Turing.Tape Symbol) : Prop :=
  ∀ j : ℤ, pos + j < -(S : ℤ) ∨ (S : ℤ) < pos + j → t.nth j = 0

private theorem support_update {S : ℕ} {pos : ℤ} {t : Turing.Tape Symbol}
    (ht : SupportedAt S pos t) (hp : -(S : ℤ) ≤ pos ∧ pos ≤ S) (write move : Symbol) :
    SupportedAt S (pos + moveDelta move) (updateTape t write move) := by
  intro j hj
  rw [LiveEvaluatorStep.updateTape_nth, ite_eq_right (by omega)]
  exact ht _ (by omega)

private theorem support_step (p : Program) {c : Config p.extra} (b : Bool) {S : ℕ} {x y : ℤ}
    (h : HeadBox S x y) (hx : SupportedAt S x c.firstTape) (hy : SupportedAt S y c.secondTape) :
    let m := choiceMotion p c b
    let c' := choiceStep p c b
    SupportedAt S (x + m.1) c'.firstTape ∧ SupportedAt S (y + m.2) c'.secondTape := by
  dsimp only
  by_cases ha : c.state.val = 1
  · have hr : ¬ 2 ≤ c.state.val := by omega
    cases b <;> simpa [choiceStep, choiceMotion, ha, hr, reject] using And.intro hx hy
  by_cases hz : c.state.val = 0
  · simpa [choiceStep, choiceMotion, hz] using And.intro hx hy
  have hr : 2 ≤ c.state.val := by omega
  have go (a : Instruction p.extra) :
      SupportedAt S (x + moveDelta a.firstMove) (advance c a).firstTape ∧
      SupportedAt S (y + moveDelta a.secondMove) (advance c a).secondTape :=
    ⟨support_update hx ⟨h.1, h.2.1⟩ _ _, support_update hy h.2.2 _ _⟩
  simp only [choiceStep, choiceMotion, ha, hz, hr, ite_false, ite_true]
  cases row : branches p c <;> cases b <;> simp [chosenInstruction, reject] <;> first
    | exact ⟨hx, hy⟩
    | exact go _

private theorem fits_of_supported {R S : ℕ} {pos : ℤ} {t : Turing.Tape Symbol}
    (h : SupportedAt S pos t) (hp : -(R : ℤ) ≤ pos ∧ pos ≤ R) : TapeFits (S + R) t := by
  intro j hj
  exact h _ (by push_cast at hj; omega)

private theorem canonical_fits {p M : ℕ} (c : Config p) (h : ConfigFits M c) :
    StateFits M (canonical c) := by
  unfold canonical
  split
  · trivial
  split
  · trivial
  exact ⟨by omega, h⟩

private theorem history_fits_from (p : Program) {R S : ℕ} (hRS : R ≤ S)
    (t : ℕ) (c : Config p.extra) (x y : ℤ) (hx : SupportedAt S x c.firstTape)
    (hy : SupportedAt S y c.secondTape)
    (hbox : ∀ bits, let d := choiceDisplacement p c bits; HeadBox R (x + d.1) (y + d.2))
    (w : Fin t → Bool) (i : Fin (t + 1)) : StateFits (S + R) (history p t c w i) := by
  induction t generalizing c x y
  all_goals
    have h : HeadBox R x y := by simpa [choiceDisplacement] using hbox []
    have hS : HeadBox S x y := by
      unfold HeadBox at *
      omega
    have hc : StateFits (S + R) (canonical c) := canonical_fits _
      ⟨fits_of_supported hx ⟨h.1, h.2.1⟩, fits_of_supported hy h.2.2⟩
  case zero => exact hc
  case succ t ih =>
    refine Fin.cases hc (fun j => ?_) i
    have hs := support_step p (w 0) hS hx hy
    apply ih _ _ _ hs.1 hs.2
    intro bits
    simpa [choiceDisplacement, add_assoc] using hbox (w 0 :: bits)

private theorem initial_support (s : List Symbol) (S : ℕ) (hs : s.length ≤ S) :
    SupportedAt S 0 (Turing.Tape.mk₁ s) := by
  intro j hj
  cases j with
  | ofNat n =>
    change (0 : ℤ) + (n : ℤ) < -(S : ℤ) ∨ (S : ℤ) < 0 + (n : ℤ) at hj
    change (Turing.Tape.mk' _ _).nth (n : ℤ) = _
    rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_default _ (by omega)]
    rfl
  | negSucc n =>
    change (Turing.ListBlank.mk ([] : List Symbol)).nth n = 0
    rw [Turing.ListBlank.nth_mk, List.getI_eq_default _ (by simp)]
    rfl

/-- Any evaluator whose heads remain within radius `R` has canonical bounded
cut configurations on every branch, for every clock. -/
theorem history_fits (p : Program) (raw : Word) (R : ℕ)
    (bounded : ∀ bits, let d := choiceDisplacement p (initial p raw) bits; HeadBox R d.1 d.2)
    (t : ℕ) (w : Fin t → Bool) (i : Fin (t + 1)) :
    StateFits (raw.length + R + R) (history p t (initial p raw) w i) := by
  apply history_fits_from p (Nat.le_add_left ..) t _ 0 0
  · apply initial_support
    simp
  · apply initial_support
    simp
  · intro bits
    simpa using bounded bits

/-- On the literal machine compiled from a finite stack evaluator, a bound on
the total stack storage supplies the cut window independently of its time. -/
theorem history_fits_labeled {K Q : Type*} [DecidableEq K] [Fintype K] [Fintype Q]
    (input : K) (code : StackCode K Q) (start : Q) (raw : Word) {B : ℕ}
    (bounded : ∀ ⦃q s⦄, Reach code start (labeledInput input raw) q s →
      Fintype.card K + 1 + ∑ a, (s a).length ≤ B)
    (t : ℕ) (w : Fin t → Bool) (i : Fin (t + 1)) :
    let p := labeledProgram input code start
    StateFits (raw.length + (7 * B + 4) + (7 * B + 4)) (history p t (initial p raw) w i) :=
  history_fits _ _ _ (input_space_labeled input code start raw bounded) t w i

end LiveEvaluatorSpace

end VPVNP
end Computability
end OAI
