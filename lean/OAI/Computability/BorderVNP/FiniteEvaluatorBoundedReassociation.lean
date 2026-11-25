import OAI.Computability.BorderVNP.FiniteEvaluatorBoundedSequence

/-! # Moving a sequence boundary in a compiled field evaluator

Rebracketing a list of stages preserves each real event history, both returned
states, the three charged limits and every field scalar. Each side fetches
private calls from its own emitted program counter table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamContraction
open scoped BigOperators Classical

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]
variable (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)

private theorem reassociate_run (mac : TeamOpcode.Macros w 8) (stages : List Code) (a b : Code) {s mem es t mt} :
    Runs pub mac (stages.foldr Code.seq (.seq a b)) s mem es t mt ↔
      Runs pub mac (.seq (stages.foldr Code.seq a) b) s mem es t mt := by
  induction stages generalizing s mem es t mt with
  | nil => rfl
  | cons c cs ih =>
    constructor
    · intro r
      obtain ⟨u,mu,fs,gs,rfl,first,rest⟩ := Runs.seq_iff.mp r
      obtain ⟨v,mv,hs,ys,rfl,mid,last⟩ := Runs.seq_iff.mp (ih.mp rest)
      exact List.append_assoc .. ▸ (first.seq mid).seq last
    · intro r
      obtain ⟨v,mv,xs,ys,rfl,left,last⟩ := Runs.seq_iff.mp r
      obtain ⟨u,mu,fs,hs,rfl,first,mid⟩ := Runs.seq_iff.mp left
      exact (List.append_assoc ..).symm ▸ first.seq (ih.mpr (mid.seq last))

/-- On each physical returning run, moving the final sequence boundary retains
the fetched field product, including the individual private routine identifiers. -/
theorem reassociate_weight (stages : List Code) (a b : Code) {s mem es t mt}
    (run : Runs pub (TeamSiteEvents.macros lib fuel) (stages.foldr Code.seq (.seq a b)) s mem es t mt) :
    weight pub lib ret fuel (stages.foldr Code.seq (.seq a b)) s es =
      weight pub lib ret fuel (.seq (stages.foldr Code.seq a) b) s es := by
  induction stages generalizing s mem es t mt with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨u,mu,fs,gs,rfl,first,rest⟩ := Runs.seq_iff.mp run
    obtain ⟨v,mv,hs,ys,rfl,mid,last⟩ := Runs.seq_iff.mp ((reassociate_run pub (TeamSiteEvents.macros lib fuel) cs a b).mp rest)
    simp only [List.foldr_cons]
    rw [weight_seq pub lib ret fuel first rest,ih rest,weight_seq pub lib ret fuel mid last,
      ← List.append_assoc,weight_seq pub lib ret fuel (first.seq mid) last,weight_seq pub lib ret fuel first mid,mul_assoc]

/-- Changing a bracket in the physical stage sequence preserves each returning
history and its complete final state, also with the exact three cutoffs. -/
noncomputable def reassociateEquiv (mac : TeamOpcode.Macros w 8) (stages : List Code) (a b : Code) (s : Bank w) (mem : Memory w)
    (ticks burst clock : ℕ) :
    Evaluator.BoundedReturns (stages.foldr Code.seq (.seq a b)) pub mac s mem ticks burst clock ≃
      Evaluator.BoundedReturns (.seq (stages.foldr Code.seq a) b) pub mac s mem ticks burst clock := by
  let E : Evaluator.Returns (stages.foldr Code.seq (.seq a b)) pub mac s mem ≃
      Evaluator.Returns (.seq (stages.foldr Code.seq a) b) pub mac s mem :=
    Equiv.subtypeEquivRight fun _ => reassociate_run pub mac stages a b
  exact E.subtypeEquiv fun _ => Iff.rfl

/-- Every charged history retains all original events, registers and shared
memory under the sequence reassociation. -/
theorem reassociateEquiv_val (mac : TeamOpcode.Macros w 8) (stages : List Code) (a b : Code) (s : Bank w) (mem : Memory w)
    (ticks burst clock : ℕ) (x : Evaluator.BoundedReturns (stages.foldr Code.seq (.seq a b)) pub mac s mem ticks burst clock) :
    (reassociateEquiv pub mac stages a b s mem ticks burst clock x).val.val = x.val.val := rfl

/-- Exact bounded sum equality for a finite list of linked source fragments, with
identical post-state and trace costs on both sides of the regrouping. -/
theorem reassociate_boundedWeight (stages : List Code) (a b : Code) (s : Bank w) (mem : Memory w)
    (ticks burst clock : ℕ) :
    boundedWeight pub lib ret fuel (stages.foldr Code.seq (.seq a b)) s mem ticks burst clock =
      boundedWeight pub lib ret fuel (.seq (stages.foldr Code.seq a) b) s mem ticks burst clock := by

  let left := stages.foldr Code.seq (.seq a b)
  let right := Code.seq (stages.foldr Code.seq a) b
  let mac := TeamSiteEvents.macros (w := w) lib fuel
  let charged := reassociateEquiv pub mac stages a b s mem ticks burst clock
  let := Fintype.ofFinite (Evaluator.BoundedReturns left pub mac s mem ticks burst clock)
  let := Fintype.ofFinite (Evaluator.BoundedReturns right pub mac s mem ticks burst clock)
  unfold boundedWeight
  apply Finset.sum_equiv charged (by simp)
  exact fun x _ => reassociate_weight pub lib ret fuel stages a b x.val.property

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
