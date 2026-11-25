import OAI.Computability.BorderVNP.FiniteProcessorWeightRun
import OAI.Computability.BorderVNP.TeamContractionReadout
import OAI.Computability.BorderVNP.TeamSiteEvents
import OAI.Computability.BorderVNP.TeamSiteChunk

/-! # Native finite-field path weights with the actual adaptive routine identifier

The signed external event records its old words and choice tape. Its source
program counter determines which private routine computes the field factor.
Replaying the architectural transitions retains that information at every call.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP TeamSite TeamRAM TeamPrivateFragment TeamPrivateTape TeamContraction
open VPVNP.BurstRAM (Word)
open scoped BigOperators Classical

variable {Q Γ : Type} {p r k a m g width : ℕ} {F : Type*} [Field F]

omit [Field F] in
private theorem track_isSome {d : ℕ} {T : Table Q d} {n q t bs out u} (h : Run T n q t bs out u)
    (w : Q → (Fin d → Bool) → Bool → F) (fuel : ℕ) (hf : n < fuel) :
    (trackReturn T w fuel q t bs).isSome = out.isSome := by
  induction h generalizing fuel with
  | @stop q t ok sg op =>
    cases fuel with
    | zero => omega
    | succ f => cases ok <;> simp [trackReturn,op]
  | one op _ ih =>
    cases fuel with
    | zero => omega
    | succ f => simpa only [trackReturn,op] using ih f (by omega)
  | two b op _ ih =>
    cases fuel with
    | zero => omega
    | succ f => simpa only [trackReturn,op] using ih f (by omega)

/-- The selected native routine sees its actual words and its own exact branch tape. -/
noncomputable def returned (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) (fuel : ℕ) (e : Event width) : Option F :=
  FieldSelect.nativeReturn M.table M.alphabet.blank w fuel M.start
    (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits e.old)) e.choices

/-- Scalar factor of the source instruction fetched at the actual program counter. -/
noncomputable def eventWeight (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ)
    (tag : TeamOpcode.Exit p r a) (e : Event width) : F :=
  match tag with
  | .call j .. => (returned (lib j) (w j) fuel e).getD 0
  | _ => (e.sign.value : F)

/-- The factor added by the field instrumentation of that same private instruction. -/
noncomputable def eventAdjustment (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ)
    (tag : TeamOpcode.Exit p r a) (e : Event width) : F :=
  match tag with
  | .call j .. => adjustment (signBit e.sign) (returned (lib j) (w j) fuel e)
  | _ => 1

/-- On a fetched native transition, the signed event weight times the processor's
correction is precisely the original finite-field value, even on a zero return. -/
theorem event_eq (P : TeamOpcode.Program p r k a) (pub : Fin k → Word width)
    (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ)
    (s next : TeamOpcode.State width p r) (e : Event width)
    (adv : (P.fetch pub (TeamSiteEvents.macros lib fuel) s).advance e.choices e.old = some (next,e.sign)) :
    eventWeight lib w fuel (TeamOpcode.prepare P pub s).1 e = (e.sign.value : F) * eventAdjustment lib w fuel (TeamOpcode.prepare P pub s).1 e := by
  rw [← TeamOpcode.prepare_action] at adv
  cases tag : (TeamOpcode.prepare P pub s).1 with
  | native | sign => simp [eventWeight,eventAdjustment]
  | call j addr len pc =>
    simp only [tag,TeamOpcode.Exit.action,Instr.advance] at adv
    split at adv <;> try contradiction
    obtain ⟨sg,eval,eq⟩ := Option.map_eq_some_iff.mp adv
    have hs : sg = e.sign := congrArg Prod.snd eq
    obtain ⟨n,hn,out,u,native,hsg⟩ := ((lib j).eval_iff ..).mp eval
    have hnz := track_isSome native (fun q h b => w j q (symbols (lib j).alphabet h) b) fuel hn
    unfold Macro.initial at hnz
    rw [trackReturn_eq] at hnz
    change (returned (lib j) (w j) fuel e).isSome = out.isSome at hnz
    rw [← hs,← hsg]
    cases out with
    | none =>
      have hz : returned (lib j) (w j) fuel e = none := by cases hz : returned (lib j) (w j) fuel e <;> simp_all
      simp [eventWeight,eventAdjustment,hz,TeamPrivateCall.sign,Sign.value,signBit]
    | some sg =>
      obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp hnz
      cases sg <;> simp [eventWeight,eventAdjustment,hz,← hs,← hsg,TeamPrivateCall.sign,Sign.value,signBit,adjustment,signed]

/-- Fold native event factors by reconstructing the actual next program counter
and registers at every branch, including data-dependent read instructions. -/
noncomputable def foldEvents (P : TeamOpcode.Program p r k a) (pub : Fin k → Word width)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (factor : TeamOpcode.Exit p r a → Event width → F) :
    TeamOpcode.State width p r → List (Event width) → F
  | _, [] => 1
  | s, e :: es => match (P.fetch pub (TeamSiteEvents.macros lib fuel) s).advance e.choices e.old with
    | none => 0
    | some (next,_) => factor (TeamOpcode.prepare P pub s).1 e * foldEvents P pub lib fuel factor next es

/-- Full source-side field product along an adaptive architectural path. -/
noncomputable def pathProduct (P : TeamOpcode.Program p r k a) (pub : Fin k → Word width)
    (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ) :=
  foldEvents P pub lib fuel (eventWeight lib w fuel)

/-- The processor's sign compensation multiplies over the true fetched private calls. -/
theorem pathProduct_eq (P : TeamOpcode.Program p r k a) (pub : Fin k → Word width)
    (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ)
    (s : TeamOpcode.State width p r) (es : List (Event width))
    (localSteps : Local (P.fetch pub (TeamSiteEvents.macros lib fuel)) s es) :
    pathProduct P pub lib w fuel s es = (pathWeight es : F) * foldEvents P pub lib fuel (eventAdjustment lib w fuel) s es := by
  induction es generalizing s with
  | nil => simp [pathProduct,foldEvents,pathWeight]
  | cons e es ih =>
    obtain ⟨_,next,adv,tail⟩ := localSteps
    simp only [pathProduct,foldEvents,adv,pathWeight,List.map_cons,List.prod_cons,Function.comp_apply,Int.cast_mul]
    rw [event_eq P pub lib w fuel s next e adv]
    have eq := ih next tail
    change foldEvents P pub lib fuel (eventWeight lib w fuel) next es = _ at eq
    rw [eq]
    unfold pathWeight
    ring

/-- Discarding signed-zero native paths preserves the full field-valued sum.
A genuine private return of scalar zero at a successful signed halt remains
among the indexed paths with its exact choice bits. -/
theorem sum_nonzero (P : TeamOpcode.Program p r k a) (pub : Fin k → Word width)
    (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) (fuel : ℕ)
    (start : TeamOpcode.State width p r) (I : ℕ) (header : ℕ → Word width) (ticks burst clock : ℕ) :
    let M : MachineInput width (TeamOpcode.State width p r) := ⟨P.fetch pub (TeamSiteEvents.macros lib fuel),start,I,header⟩
    letI := Fintype.ofFinite (NativePath M ticks burst clock)
    (∑ z : NativePath M ticks burst clock, pathProduct P pub lib w fuel start z.val) =
      ∑ z : NonzeroPath M ticks burst clock, pathProduct P pub lib w fuel start z.val.val := by
  intro M
  let := Fintype.ofFinite (NativePath M ticks burst clock)
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z : NativePath M ticks burst clock => pathWeight z.val ≠ 0)
    (fun z => pathProduct P pub lib w fuel start z.val)]
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro z _
  have eq : pathWeight z.val.val = 0 := not_ne_iff.mp z.property
  rw [pathProduct_eq _ _ _ _ _ _ _ (execute_spec z.val.property.1).1,eq,Int.cast_zero,zero_mul]

end FieldProcessor

end BorderVNP
end Computability
end OAI
