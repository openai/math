import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhase
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseLists

/-! # Computability of the entry address of the alphabet simulator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase

open CommonAlphabet

variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
variable (ha : Computable fun x => (a x).size) (hq : Computable fun x => (q x).size)
variable (c : ∀ x, Code (A x)) (hw : Computable fun x => (c x).width)
local notation "num" => fun x => Numbering.controller (a x) (q x) i (Code.width (c x))
local notation "p" => states a q i (fun x => Code.width (c x)) (ha := ha) (hq := hq) (hw := hw)

include ha hq hw in
theorem readStart_size : Computable fun x => (num x).size := (p).size_eff

include ha hq hw in
/-- All counters begin at zero and every read buffer contains the blank trit.
The entry address is computable even when each source family member uses a
different alphabet and a different block length. -/
theorem readStart_rank (entry : ∀ x, Q x) (he : Computable fun x => ((q x).equiv (entry x)).val) :
    Computable fun x => ((num x).equiv (readStart (c x) (entry x))).val := by
  have empty : Computable fun x => List.replicate i.size (List.replicate (c x).width (0:ℕ)) :=
    computable_replicate (Computable.const _) (computable_replicate hw (Computable.const _))
  have data : Computable fun x => read ((q x).equiv (entry x)).val
      (List.replicate i.size (List.replicate (c x).width 0)) 0 :=
    Computable.sumInr.comp (Computable.sumInr.comp (Computable.sumInl.comp
      (he.pair (empty.pair (Computable.const 0)))))
  apply ((p).encode_eff.comp Computable.id data).of_eq
  intro x
  rw [← (p).encode_view x (readStart (c x) (entry x)),states_view]
  change _ = (p).encode x (read _ (i.all.map fun _ =>
    (List.finRange (c x).width).map fun _ => (0:ℕ)) 0)
  simp [Numbering.all, Function.comp_def]

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
