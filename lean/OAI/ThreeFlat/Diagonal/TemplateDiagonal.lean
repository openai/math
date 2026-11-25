import OAI.ThreeFlat.Diagonal.BlockChronology
import OAI.ThreeFlat.Diagonal.PhysicalDefect
import OAI.ThreeFlat.Diagonal.TickPins

namespace OAI
/-! # The block approximation inequality for a genuine team tick template -/

namespace ThreeFlat.Diagonal

variable {F I β : Type*} [Field F] [Fintype I] [DecidableEq I] {a p q n : ℕ}

/-- Chronological products of genuine single-chunk transitions, with the
auxiliary word initialized and tested for zero. -/
noncomputable def templateRun (N : BitNetwork F p) (blocks : List β)
    (slot : β → Fin n → I) (active : β → Bool)
    (pin : β → Fin n → Fin q → BitString a → BitString a → BitString a → BitString a → Fin p → Bool) :
    Matrix (Bool → I → BitString a) (Bool → I → BitString a) F :=
  ((blocks.map fun t => (List.ofFn fun i => physicalTick (active t) (slot t i) (teamTick N (pin t) i)).prod).prod).submatrix
    (fun x => (x, fun _ => false)) (fun y => (y, fun _ => false))

theorem templateRun_eq_fixings (N : BitNetwork F p) (blocks : List β) (slot : β → Fin n → I)
    (active : β → Bool) (distinct : ∀ t, Function.Injective (slot t))
    (pin : β → Fin n → Fin q → BitString a → BitString a → BitString a → BitString a → Fin p → Bool) :
    templateRun N blocks slot active pin = physicalRun blocks slot active
      (fun t f => fixingWeight (teamTick N (pin t)) f • (1 : Matrix (I → BitString a) (I → BitString a) F)) := by
  unfold templateRun physicalRun
  simp only [physical_ticks_eq_fixings _ (distinct _) ]

/-- If the catalytic entry has the promised per-fixing defect for every
input to the common template, then its evaluator cannot be simulated with
an extra identity branch by the actual chronological ticks. The catalyst
is the full inactive external half, and it alternates with `active`. -/
theorem template_replacement_ne_identity_add (N : BitNetwork F p) (blocks : List β)
    (slot : β → Fin n → I) (active : β → Bool) (distinct : ∀ t, Function.Injective (slot t))
    (pin : β → Fin n → Fin q → BitString a → BitString a → BitString a → BitString a → Fin p → Bool)
    (X : (Fin n → Fin q → Fin p → Bool) → Matrix (I → BitString a) (I → BitString a) F)
    {w d : ℕ} (ha : a = 2 ^ (w ^ 10 - w ^ 4)) (hw : d + 8 ≤ w) (hn : 1 ≤ n) (hmax : n ≤ w ^ d)
    (hsave : 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w) ≤ a * Fintype.card I)
    (nsteps : blocks.length ≤ 2 ^ (w ^ 6) / n)
    (approx : ∀ pins, (X pins - (∏ i, ∏ j, N.eval (pins i j)) • 1).rank ≤
      2 ^ (a * Fintype.card I - 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w))) :
    templateRun N blocks slot active pin ≠
      1 + physicalRun blocks slot active (fun t f => X (fixingPins (pin t) f)) := by
  rw [templateRun_eq_fixings _ _ _ _ distinct]
  apply physical_replacement_ne_identity_add blocks slot active _ _ ha hw hn hmax hsave nsteps
  intro t _ f
  rw [fixingWeight_eq_template_product]
  exact approx _

end ThreeFlat.Diagonal

end OAI
