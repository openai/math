import OAI.Computability.BorderVNP.FiniteProcessorRegions
import OAI.Computability.BorderVNP.TeamSiteProcessorRowSupply

/-! # Field output after all checks of a successful real processor row

The exact signed row model already runs the final frame and physical sort tests.
Its deterministic suffix is recovered after the supplied weighted replay reaches
a retired block, and all of those remaining rows preserve the field accumulator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateFragment
open FieldStack (AllNext allNext_rename)
open private step_unique from OAI.Computability.BorderVNP.TeamContractionReplayRun
open private allNext_map from OAI.Computability.BorderVNP.FiniteProcessorRegions

variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {F : Type*} [Field F] [Fintype F]

/-- After its live loop, a processor can only verify its frame and sorting fields. -/
def retired {P : TeamOpcode.Program p r k a} : Processor.Label P Q m g → Prop
  | .block (.finish ..) | .block (.done _) | .block .invalid | .close .. | .sort .. | .reject => True
  | _ => False

private theorem retired_closed (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (q : Processor.Label P Q m g) (h : retired q) : AllNext retired (Processor.code P lib q) := by
  cases q with
  | block q =>
    cases q with
    | finish sg q =>
      simp only [Processor.code,allNext_map]
      cases q <;> simp only [Endpoint.code] <;> first
        | exact allNext_rename _ _ _ _ (fun _ => trivial)
        | (rename_i ok; cases ok <;> trivial)
    | _ => first | exact h.elim | trivial
  | close _ _ => apply allNext_rename; intro z; cases z <;> trivial
  | sort _ _ => exact allNext_rename _ _ _ _ (fun _ => trivial)
  | reject => trivial
  | _ => exact h.elim

private theorem completion {K S : Type} [DecidableEq K] {C : StackCode K S}
    {k t q s mid b endQ out ok} (h : StackRuns C k q s mid b) (full : StackRuns C t q s endQ out)
    (halt : C endQ = .halt ok) : ∃ u, k+u=t ∧ StackRuns C u mid b endQ out := by
  induction h generalizing t with
  | nil => exact ⟨_,by simp,full⟩
  | cons step _ ih =>
    cases full with
    | nil => cases step <;> simp_all
    | cons step' next =>
      obtain ⟨rfl,rfl⟩ := step_unique step step'
      obtain ⟨u,hu,run⟩ := ih next
      exact ⟨u,by omega,run⟩

/-- A passing signed row model and the actual weighted prefix to its retired block
give a complete accepting leaf of the full field validator. Its final scalar is
the accumulated field element times the original sorter sign. -/
theorem accepted_leaf (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (X : Processor.Row.Context P lib n d e w) (bits : List Bool) (sg : Option Bool) (pass : Prop)
    (clock : ℕ) (model : X.Model bits sg pass clock) (ok : pass) (hnz : sg.isSome = true)
    {k mid bank} (endAcc : F) (done : retired mid)
    (prefixRun : StackRuns (replay (code P lib weights)) k
      ((Processor.start,Fintype.equivFin F 1),bits) (StackCompiler.labeledInput Layout.input X.raw)
      ((mid,Fintype.equivFin F endAcc),[]) bank) :
    (bits, endAcc * (if sg.getD false then -1 else 1)) ∈ FieldReplay.leaves (code P lib weights)
      (FieldStack.productOutput (factor lib weights) terminal) clock (Processor.start,Fintype.equivFin F 1)
      (StackCompiler.labeledInput Layout.input X.raw) := by
  obtain ⟨t,ht,q,out,b,full,halt,accept,check,_⟩ := model
  obtain rfl := accept.mpr ⟨ok,hnz⟩
  obtain ⟨z,rfl,_⟩ := (check sg).mpr ⟨ok,rfl⟩
  have pre := FieldStack.replay_project (Processor.code P lib) (factor lib weights) prefixRun
  have termRow : replay (Processor.code P lib) (.sort sg (some z),[]) = .halt true := by simp [replay,halt]
  obtain ⟨u,he,tail⟩ := completion pre full termRow
  have ending := FieldStack.neutral_forward (Processor.code P lib) (factor lib weights) retired endAcc
    (fun q h => by cases q with
                   | block q => cases q <;> first | rfl | exact h.elim
                   | _ => rfl) (retired_closed P lib) tail done
  apply (FieldReplay.mem_leaves_iff ..).mpr
  refine ⟨_,he ▸ ht,_,_,prefixRun.trans ending,?_,?_⟩
  · simp [code,FieldStack.productCode,halt,StackOp.rename]
  · cases hs : sg.getD false <;> simp [FieldStack.productOutput,factor,terminal,Processor.negative,hs]

end FieldProcessor

end BorderVNP
end Computability
end OAI
