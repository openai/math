import OAI.Computability.VPVNP.LivePhysicalRoutes
import OAI.Computability.VPVNP.LivePhysicalUnit
import OAI.Computability.VPVNP.LiveActiveGroupCounts

/-!
# Assembling the native local count on every physical cut assignment

Only the two active continuations enter the assembly. They start in the real
post-header memory at the corresponding native stage. The unit branch, mixed
modes, malformed padding and the incoming-cut condition are discharged here.
The cap on each continuation includes the actual preceding header and router
reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.LocalCount
open BurstRAM LiveHeaderSchedule LiveHeaderProgram LiveHeader ChainAssignments
open ExponentTrace LiveChain LiveEvaluatorEncoding PairStages
open scoped Classical

/-- The evaluated live-header sizes governing this group's cuts and advice. -/
abbrev profile (G : Group) := Header.sizes G.constants G.g

/-- Physical address, clock and bucket bounds needed by the checked header. -/
structure Conditions (G : Group) (S H : ℕ) : Prop where
  word : 4 ≤ G.g.w
  clock : 154 ≤ G.clock
  bounds : Fields.Bounds (profile G) (Header.base G.g) G.g.d G.g.w
  indices : (profile G).h+2 ≤ 2^G.g.d
  advice : (profile G).advice ≤ 2^G.g.d
  tags : stages.length ≤ 2^G.g.w
  cost : costBound (profile G)+3 ≤ S*H
  call : 11 ≤ H

variable {G : Group} {S H t Z M : ℕ} {Nom : Type*} [Fintype Nom]
variable {Path : Exterior (profile G).h (profile G).delta → Fin (2^(profile G).h) → Nom → Type*}
variable [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- State of the checked physical prefix from which a pair or tail routine
actually starts. The same object gives the accumulated report cap and tag. -/
abbrev Prepared (W : Conditions G S H) (adv : CutSchedule.Bits (profile G).advice)
    (cuts : AllCuts (profile G).h (profile G).delta) (j : Fin (2^((profile G).h+1))) (mode : Header.ActiveMode) :=
  Header.PrefixTrace G (physicalMemory (d := G.g.d) W.word adv cuts j) mode.stage
    (callBound (profile G)+1) (costBound (profile G)+4)

/-- The actual continuation memory obtained by replaying the prepared header reports on the
distributed input. -/
abbrev memory {W : Conditions G S H} {adv : CutSchedule.Bits (profile G).advice}
    {cuts : AllCuts (profile G).h (profile G).delta} {j : Fin (2^((profile G).h+1))}
    {mode : Header.ActiveMode} (tr : Prepared W adv cuts j mode) :=
  after (physicalMemory (d := G.g.d) W.word adv cuts j) (eventLog tr.logs)

/-- Accepted continuations from the prepared memory whose reports fit the caps together with
the preceding header reports. -/
abbrev remaining {W : Conditions G S H} {adv : CutSchedule.Bits (profile G).advice}
    {cuts : AllCuts (profile G).h (profile G).delta} {j : Fin (2^((profile G).h+1))}
    {mode : Header.ActiveMode} (tr : Prepared W adv cuts j mode) :=
  ActualPaths G.P G.clock 0 (memory tr) (fun rs => withinCaps S H (tr.logs++rs))

/-- The first-half proof obligation after mode and padding validation. -/
def PairContinuation (W : Conditions G S H) (adv : CutSchedule.Bits (profile G).advice)
    (fit : 1+t*Z ≤ (profile G).delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ) : Prop :=
  ∀ (cuts : AllCuts (profile G).h (profile G).delta) (i : Fin (2^(profile G).h)),
    let j := halves (profile G).h (.inl i)
    physicalTag cuts j = some .pair → (∀ side, Fields.ValidPadding (profile G) cuts j .pair side) →
    ∀ tr : Prepared W adv cuts j .pair,
      Output (profile G) (Header.base G.g) G.g.d W.word adv cuts j .pair (memory tr) →
      Nat.card (remaining tr) = pairCount fit inc (liveCutEquiv (profile G).h (profile G).delta cuts).1 i

/-- The second-half proof obligation, including a possible malformed
incoming configuration and the final group's accepting endpoint. -/
def TailContinuation (W : Conditions G S H) (adv : CutSchedule.Bits (profile G).advice)
    (fit : 1+t*Z ≤ (profile G).delta)
    (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w (profile G).delta)
    (init : (Fin t → ℕ) → Code G.evaluator.extra M) : Prop :=
  ∀ (cuts : AllCuts (profile G).h (profile G).delta) (i : Fin (2^(profile G).h)),
    let j := halves (profile G).h (.inr i)
    let b := liveCutEquiv (profile G).h (profile G).delta cuts
    physicalTag cuts j = some .tail → (∀ side, Fields.ValidPadding (profile G) cuts j .tail side) →
    ∀ tr : Prepared W adv cuts j .tail,
      Output (profile G) (Header.base G.g) G.g.d W.word adv cuts j .tail (memory tr) →
      Nat.card (remaining tr) = tailCount G.evaluator layout (init (fun a => (counters fit b.1 (Fin.last _) a).val)) b.2 i

variable (W : Conditions G S H) (adv : CutSchedule.Bits (profile G).advice)
variable (fit : 1+t*Z ≤ (profile G).delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
variable (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w (profile G).delta)
variable (init : (Fin t → ℕ) → Code G.evaluator.extra M)
variable (he : (profile G).e = t*Z) (hc : (profile G).config = fieldWords M*G.w)
include he hc

private theorem active (cuts : AllCuts (profile G).h (profile G).delta) (j : Fin (2^((profile G).h+1)))
    (mode : Header.ActiveMode) (sel : physicalTag cuts j = some mode.tag)
    (body : (∀ side, Fields.ValidPadding (profile G) cuts j mode.tag side) →
      ∀ tr : Prepared W adv cuts j mode,
        Output (profile G) (Header.base G.g) G.g.d W.word adv cuts j mode.tag (memory tr) →
        Nat.card (remaining tr) = groupEvaluation fit inc G.evaluator layout init cuts j) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (physicalMemory (d := G.g.d) W.word adv cuts j) (withinCaps S H)) =
      specifiedGroupCount fit inc G.evaluator layout init cuts j := by
  by_cases good : ∀ side, Fields.ValidPadding (profile G) cuts j mode.tag side
  · obtain ⟨tr,out⟩ := Header.active_prefix G W.word W.clock adv cuts j W.bounds W.indices W.advice W.tags mode sel good
    rw [Fields.specified_eq_evaluation (tag := mode.tag) (by cases mode <;> decide) he fit inc layout init cuts j sel (good .left)]
    rw [← G.program_eq]
    exact (Nat.card_congr (tr.equiv (withinCaps S H)).symm).trans (body good tr out)
  · have invalid : ¬ ∃ tag, physicalTag cuts j = some tag ∧ ∀ side, Fields.ValidPadding (profile G) cuts j tag side := by
      rintro ⟨tag,hs,hv⟩
      rw [sel] at hs
      obtain rfl := Option.some.inj hs
      exact good hv
    rw [UnitGroup.physical_card_zero G W.word W.clock adv cuts j W.bounds W.indices W.advice W.tags invalid]
    by_contra bad
    exact good (Fields.specifiedGroupCount_ne_zero_valid he hc fit inc G.evaluator layout init sel (Ne.symm bad))

/-- The exact `group` conclusion used in `FixedModelDiagonal.LocalCertificate`
for the real instruction table, start word zero, physical memory, and native
report caps. The supplied components are confined to their valid active routes. -/
theorem group (pair : PairContinuation (Path := Path) W adv fit inc)
    (tail : TailContinuation W adv fit layout init)
    (cuts : AllCuts (profile G).h (profile G).delta) (j : Fin (2^((profile G).h+1))) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (physicalMemory (d := G.g.d) W.word adv cuts j) (withinCaps S H)) =
      specifiedGroupCount fit inc G.evaluator layout init cuts j := by
  have hd : 0 < (profile G).delta := by omega
  by_cases ev : evalCutMode cuts j.castSucc ∧ evalCutMode cuts j.succ
  · rcases (halves (profile G).h).surjective j with ⟨i,rfl⟩
    cases i with
    | inl i =>
      have hs := (physicalTag_pair hd cuts (halves (profile G).h (.inl i))).2 ⟨ev,i.isLt⟩
      apply active W adv fit inc layout init he hc cuts _ .pair hs
      intro pads tr out
      simpa only [groupEvaluation,Equiv.symm_apply_apply,Sum.elim_inl] using pair cuts i hs pads tr out
    | inr i =>
      have hhalf : 2^(profile G).h < (halves (profile G).h (.inr i)).val+1 := by
        change 2^(profile G).h < 2^(profile G).h+i.val+1; omega
      have hs := (physicalTag_tail hd cuts (halves (profile G).h (.inr i))).2 ⟨ev,hhalf⟩
      apply active W adv fit inc layout init he hc cuts _ .tail hs
      intro pads tr out
      simpa only [groupEvaluation,Equiv.symm_apply_apply,Sum.elim_inr] using tail cuts i hs pads tr out
  · rw [UnitGroup.physical_unitGroupCount G W.word W.clock adv cuts j W.bounds W.indices W.advice W.tags W.cost W.call ev]
    simp [specifiedGroupCount,← and_assoc,ev]

end LiveProgram.LocalCount

end VPVNP
end Computability
end OAI
