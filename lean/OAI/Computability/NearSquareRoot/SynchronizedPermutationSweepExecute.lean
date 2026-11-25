import OAI.Computability.NearSquareRoot.SynchronizedPermutationUniversalNative
import OAI.Computability.NearSquareRoot.PrecisionDigitCloth

/-! # One fixed bounded program for all Fourier batch descriptors and record arrays -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader.PassPoint
open IntegerMultiplication Code Adic Strip Loom FixedPoint Controlled Space PositionProgram SynchronizedPermutationBudget

noncomputable section

/-- The data transported by a pass can be an arbitrary coefficient array. -/
abbrev Input := (p : PassPoint) × (PackedAddress Unit p.fields → Record p.k)

def move (s : Input) : Input := ⟨s.1,scatter s.1.network s.2⟩

def volumeB (p : PassPoint) : ℕ := 2^p.k * (2*(componentBits p.k+1))

def beads (s : Input) : Tree :=
  stripe (line 2 s.1.k) fun a => strip (Series.natural (2*(componentBits s.1.k+1))) (Dusk.stock (s.2 (s.1.rank a)))

/-- One reserve bound is chosen before the consuming family of actual Dusk arrays.
The header is the polynomially generated Fourier pass descriptor. -/
theorem execute (ρ : ℝ) (lower : 1/2 < ρ) (upper : ρ ≤ 1) :
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → Input), (∀ y, D ≤ (pick y).1.D) →
      BoundedTask (fun y => volumeB (pick y).1 * (positionFactor ρ (pick y).1.k+rowFactor (pick y).1.k ρ+1))
        (fun y => volumeB (pick y).1)
        (fun y => .fork (send (pick y).1.descriptor) (beads (pick y)))
        (fun y => beads (move (pick y))) := by
  let u (s : Input) := Series.natural (2*(componentBits s.1.k+1))
  let val (s : Input) (a : PackedAddress Unit s.1.fields) := Dusk.stock (s.2 a)
  have count (s : Input) : (u s).count = 2*(componentBits s.1.k+1) := by simp [u]
  obtain ⟨D,run⟩ := nativeOn (fun s : Input => s.1) ρ lower upper u
    (fun s => by rw [count]; omega) val
  refine ⟨D,fun pick fit => ?_⟩
  exact (run pick fit).conform (fun _ => by simp only [count,volumeB])
    (fun _ => by simp only [Function.comp_apply,count,volumeB]) (fun _ => rfl) (fun _ => rfl)

end
end Benes.PackedBatchHeader.PassPoint

end NearSquareRoot
end Computability
end OAI
