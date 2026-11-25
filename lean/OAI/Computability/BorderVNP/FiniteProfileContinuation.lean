import OAI.Computability.BorderVNP.FiniteProfileGeometry
import OAI.Computability.BorderVNP.PackedHistoryProfileWithin
import OAI.Computability.BorderVNP.FiniteEvaluatorCellsNative

/-! # Field-valued continuations after the accepted physical profile

The finite positive branch first prepares pins and reconstructs geometry, then executes
private placement and the rest of the actual program. Every charged native path has one
such chronological decomposition. Its field weight is the continuation's field product.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction PackedHistoryCircuit GeometryAdvice
open FiniteEvaluator (weight weight_seq positive_weightedBodyEquiv)
open private seq_assoc from OAI.Computability.BorderVNP.RoutingISABlockAppend

/-- The first two commands of the finite positive body in the order actually assembled. -/
def placedBody (placement rest : Code) : Code := .seq preparePins (.seq (.seq reconstruct placement) rest)

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

theorem placedBody_split (placement rest : Code) {s m es z mz} :
    Runs pub mac (placedBody placement rest) s m es z mz ↔
      Runs pub mac (.seq pinGeometry (.seq placement rest)) s m es z mz := by
  have shift {t mt fs} : Runs pub mac (.seq (.seq reconstruct placement) rest) t mt fs z mz ↔
      Runs pub mac (.seq reconstruct (.seq placement rest)) t mt fs z mz := seq_assoc.symm
  change Runs _ _ (.seq preparePins (.seq (.seq reconstruct placement) rest)) _ _ _ _ _ ↔
    Runs _ _ (.seq (.seq preparePins reconstruct) (.seq placement rest)) _ _ _ _ _
  rw [← seq_assoc]
  simp only [Runs.seq_iff (a := preparePins),shift]

variable {Q Γ : Type} {F : Type*} [Field F] {m g : ℕ}
variable (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)
local notation "macros" => TeamSiteEvents.macros lib fuel

/-- The physical fresh guess and all gates have field weight one. Reassociation of the
opcode fragments preserves every private return identifier of the remaining computation. -/
theorem placedBody_weight (placement rest : Code) {s mem gs t mt fs z mz}
    (front : Runs pub macros pinGeometry s mem gs t mt) (tail : Runs pub macros (.seq placement rest) t mt fs z mz) :
    weight pub lib ret fuel (placedBody placement rest) s (gs++fs) = weight pub lib ret fuel (.seq placement rest) t fs := by
  obtain ⟨a,ma,p,h,hg,pins,geometry⟩ := Runs.seq_iff.mp front
  obtain ⟨b,mb,c,r,hf,place,remaining⟩ := Runs.seq_iff.mp tail
  have neutral := pinGeometry_pathProduct lib ret fuel front
  change weight pub lib ret fuel (.seq preparePins reconstruct) s gs = 1 at neutral
  rw [hg,weight_seq pub lib ret fuel pins geometry] at neutral
  rw [hg,hf,show (p++h)++(c++r) = p++((h++c)++r) by simp [List.append_assoc],placedBody,
    weight_seq pub lib ret fuel pins ((geometry.seq place).seq remaining),weight_seq pub lib ret fuel (geometry.seq place) remaining,
    weight_seq pub lib ret fuel geometry place,weight_seq pub lib ret fuel place remaining]
  rw [mul_assoc,← mul_assoc,neutral,one_mul]

variable {k o : ℕ} {bank : Bank w} {orig : Memory w}

/-- Dependent local histories after one actual substituted pin choice. -/
abbrev TailChoices (body tail : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (mem : Memory w)
    (E : (Fin k → Bool) ≃ Returns body pub mac bank mem) :=
  Σ q : Fin k → Bool, Returns tail pub mac (E q).val.2.1 (E q).val.2.2

/-- After the true wide boot and positive broadcast copy, accepted physical paths are
indexed by the checked profile's exact fresh choices and by genuine remaining field
histories on its returned memory. A malformed profile has no such path. All cutoffs
refer to the chronological events, including every private callback's actual tape. -/
theorem positive_profile_fibers {L : RoutingISA.Pins.Layout} (fields : RoutingISA.Pins.ProcessorFields L)
    (f : BroadcastFrame) (placement rest : Code) {start post after hs ready saved} (bank : Bank w)
    (boot : Runs pub macros wideStartup bank (processorMemory fields w) start post after)
    (copy : Runs pub macros readBroadcast post after hs ready saved) (stable : f.Stable (readings ready))
    (mode : (saved f.dst).val ≠ 0) (falls : (placedBody placement rest).withoutAccept = true)
    (ticks burst clock : ℕ) (fits : start.length+hs.length+2 ≤ ticks)
    (ok : Prop) (pinTicks dest : ℕ) (words : Fin o → ℕ) {resident : (Fin k → Bool) → Memory w → Prop}
    (checked : ProfilePaths pinGeometry k pub macros (Function.update ready 10 (saved f.dst)) saved ok pinTicks dest words resident) :
    let whole := placedBody placement rest
    let tail := Code.seq placement rest
    let inBank := Function.update ready 10 (saved f.dst)
    let M := processorMachine (dispatchTable wideStartup whole) pub macros bank fields
    let remaining := ticks-(start.length+hs.length+2)
    (Nonempty (NativePath M ticks burst clock) → ok) ∧
    (ok → ∃ E : (Fin k → Bool) ≃ Returns pinGeometry pub macros inBank saved,
      (∀ q, (E q).val.1.flatMap TeamRAM.Event.choices = List.ofFn q ∧ Within pinTicks 0 1 (E q).val.1 ∧
        resident q (E q).val.2.2 ∧ ∀ i, readings (E q).val.2.2 (dest+i.val) = words i) ∧
      ∃ R : {z : TailChoices pinGeometry tail pub macros inBank saved E //
          Within remaining burst clock ((E z.1).val.1++z.2.val.1)} ≃ NativePath M ticks burst clock,
      ∀ z, (R z).val = dispatchPrefix f saved start hs ++ ((E z.val.1).val.1++z.val.2.val.1) ∧
        weight pub lib ret fuel (dispatchTable wideStartup whole) bank (R z).val =
          weight pub lib ret fuel tail (E z.val.1).val.2.1 z.val.2.val.1) := by
  intro whole tail inBank M remaining
  obtain ⟨wrap,wrapped⟩ := positive_weightedBodyEquiv pub lib ret fuel whole fields f bank boot copy stable mode falls ticks burst clock fits
  let asBody : Returns (.seq pinGeometry tail) pub macros inBank saved ≃ Returns whole pub macros inBank saved :=
    Equiv.subtypeEquivRight (fun _ => (placedBody_split placement rest).symm)
  let join := seqReturnEquiv pinGeometry tail pub macros inBank saved
  constructor
  · rintro ⟨y⟩
    exact checked.passes.mp ⟨(join.symm (asBody.symm (wrap.symm y).val)).1⟩
  · intro valid
    obtain ⟨E,effects⟩ := checked.outputs valid
    let choice := Equiv.sigmaCongrLeft (β := fun v : Returns pinGeometry pub macros inBank saved =>
      Returns tail pub macros v.val.2.1 v.val.2.2) E
    let run := (choice.trans join).trans asBody
    let limited := run.subtypeEquiv (p := fun z => Within remaining burst clock ((E z.1).val.1++z.2.val.1))
      (q := fun z => Within remaining burst clock z.val.1) (fun _ => Iff.rfl)
    refine ⟨E,fun q => ⟨(effects q).1,pinGeometry_within (E q).property (effects q).2.1,
      checked.memory (E q) q (effects q).1,(effects q).2.2.2⟩,limited.trans wrap,fun z => ?_⟩
    have hw := wrapped (limited z)
    exact ⟨hw.1,hw.2.trans (placedBody_weight lib ret fuel placement rest (E z.val.1).property z.val.2.property)⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
