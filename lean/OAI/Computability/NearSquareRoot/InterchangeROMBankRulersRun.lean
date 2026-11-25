import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Strip.Room

/-! # Physical expansion of the two rulers needed for center-bank packing -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBankRulers

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims

abbrev Aux := Tally × Tally × InterchangeROMAddress.Header
abbrev Triples := (Tally × Tally × Tally) × (Tally × Tally × Tally) × InterchangeROMAddress.Header

private def finish (x : (Tally × Tally) × Aux) : Triples :=
  ((x.1.1,x.2.1,x.1.2),(x.1.1,x.2.2.1,x.1.2),x.2.2.2)

private theorem finish_easy : Easy finish := by unfold finish; fun_prop

structure Rulers where
  before : Tape
  tail : Tape
  before_solid : solid before
  tail_solid : solid tail
  aux : Aux

namespace Rulers

def source (z : Rulers) := ((shape z.before,shape z.tail),z.aux)
def result (z : Rulers) := finish ((tally (room z.before),tally (room z.tail)),z.aux)
def work (z : Rulers) := room z.before + room z.tail + size z.aux

/-- Expand the two solid dimension lists into unary row counts. The sum of
their volumes pays for both physical expansions and for duplicating both
unary rulers in the output cut descriptors. -/
theorem task : Task work (fun z => send z.source) (fun z => send z.result) := by
  let A := fun z : Rulers => (⟨z.before,z.before_solid⟩ : {t : Tape // solid t})
  let B := fun z : Rulers => (⟨z.tail,z.tail_solid⟩ : {t : Tape // solid t})
  have left := (unary.on A).left (fun z => send (shape z.tail))
  have right := (unary.on B).right (fun z => send (tally (room z.before)))
  have pair := (left.compose right).left (fun z => send z.aux)
  let values (z : Rulers) := ((tally (room z.before),tally (room z.tail)),z.aux)
  have join := pair.compose (finish_easy.on values)
  refine join.bound 12 ?_
  intro z
  change (room z.before + ((send (tally (room z.before))).count + room z.tail)) +
    size ((tally (room z.before),tally (room z.tail)),z.aux) + 1 ≤ _
  change (room z.before + (size (tally (room z.before)) + room z.tail)) +
    size ((tally (room z.before),tally (room z.tail)),z.aux) + 1 ≤ _
  simp only [size_prod,size_tally,tally_length,work]
  omega

end Rulers

open NearSquareRoot.Space

/-- A compact polynomial-time header pass followed by the two linear unary
expansions. The exponent applies only to the compact input. -/
theorem prepared_bounded {I A : Type} [Codec A]
    (seed : I → A) (rulers : I → Rulers) (cells : I → ℕ)
    (prep : A → (List Tally × List Tally) × Aux) (hp : Poly prep)
    (heq : ∀ i, prep (seed i) = (rulers i).source)
    (hbefore : ∀ i, room (rulers i).before ≤ cells i)
    (htail : ∀ i, room (rulers i).tail ≤ cells i) :
    ∃ d : ℕ, BoundedTask (fun i => cells i + (size (seed i)+1)^d)
      (fun i => cells i + (size (seed i)+1)^d) (fun i => send (seed i))
      (fun i => send (rulers i).result) := by
  obtain ⟨t,ht,program⟩ := hp
  let F (i : I) := size (seed i)
  have len := (show Poly prep from ⟨t,ht,program⟩).length.map seed
  have aux : Dom F (fun i => size (rulers i).aux) := len.mono (fun i => by
    rw [heq i]
    change size (rulers i).aux ≤ size ((shape (rulers i).before,shape (rulers i).tail),(rulers i).aux)
    simp only [size_prod]
    omega)
  obtain ⟨d,C,hC⟩ := ((Dom.base F).add (ht.map seed)).add aux
  have collect := (program.on seed).conform (fun _ => rfl) (fun _ => rfl)
    (fun i => congrArg send (heq i))
  have run := BoundedTask.of_time (collect.compose (Rulers.task.on rulers))
  refine ⟨d,run.bound (C+2) (C+2) ?_ ?_⟩
  all_goals
    intro i
    have hb := hbefore i
    have ht' := htail i
    have h := hC i
    change size (seed i) + t (seed i) + size (rulers i).aux ≤ C*(size (seed i)+1)^d at h
    have he := Nat.mul_le_mul_left C (Nat.le_add_left ((size (seed i)+1)^d) (cells i))
    change _ ≤ (C+2)*(cells i+(size (seed i)+1)^d+1)
    simp only [Rulers.work, Nat.add_mul, Nat.mul_add, Nat.mul_one] at he ⊢
    have hsize : (send (seed i)).count = size (seed i) := rfl
    omega

end InterchangeROMBankRulers

end NearSquareRoot
end Computability
end OAI
