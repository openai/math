import OAI.Computability.NearSquareRoot.ScheduleStagingFallback
import OAI.Computability.NearSquareRoot.ScheduleGeneratorRace

/-! # The literal common-alphabet schoolbook comparison at index zero -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingFallback

open IntegerMultiplication TM ScheduleMachine GeneratorInputRun Uniform.IndexedSlot
open ChunkControl (Driver)
open scoped Classical

variable (d : Driver) (I : Type) [Finite I]

noncomputable def cells := Nat.card (Axes d I)*(2*space+1)

noncomputable abbrev input (n : ℕ) (x : ScheduleMachine.Input n) :=
  initialConfig start (ports d I).inp (ports d I).bit (ports d I).sep (ports d I).blank (xbits x) (ybits x)

omit [Finite I] in
theorem sound (n : ℕ) (x : ScheduleMachine.Input n) {u z}
    (hist : Trace (advance (machine d I)) (input d I n x) u z) (halt : advance (machine d I) z = none) :
    ∃ w, Source.Valid n x w ∧ whole (ports d I).blank (w.map (ports d I).bit) (z.tape (ports d I).out) := by
  obtain ⟨t,y,_,run,stop,out⟩ := runs d I n x
  obtain ⟨_,rfl⟩ := halting_trace_unique hist halt run.1 stop
  let a := (xbits x,ybits x)
  refine ⟨Lea.answer a,?_,?_⟩
  · exact (ProductRecovery.product_postcondition_iff _ _ _ (xbits_length x) (ybits_length x)).mpr rfl
  · rw [out]
    rfl

theorem completes (n : ℕ) (x : ScheduleMachine.Input n) :
    ∃ t y, t+1 ≤ time*(n+1)^2 ∧ Trace (advance (machine d I)) (input d I n x) t y ∧
      advance (machine d I) y = none ∧ VisitsAtMost (machine d I) (input d I n x) t (cells d I*(n+1)) := by
  let : Fintype (Axes d I) := Fintype.ofFinite _
  obtain ⟨t,y,ht,path,halt,_⟩ := runs d I n x
  refine ⟨t,y,ht,path.1,halt,?_⟩
  obtain ⟨v,card,covered⟩ := visitsAtMost_of_common_fence
    (-((space*(n+1):ℕ):ℤ)) (((space*(n+1):ℕ):ℤ)) path.2
  refine ⟨v,card.trans ?_,covered⟩
  unfold cells
  rw [Nat.card_eq_fintype_card,Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  let b := space*(n+1)
  change ((b:ℤ)+1-(-b)).toNat ≤ _
  rw [show ((b:ℤ)+1-(-b)).toNat = 2*b+1 by omega]
  dsimp only [b]
  nlinarith

end StagingFallback

end NearSquareRoot
end Computability
end OAI
