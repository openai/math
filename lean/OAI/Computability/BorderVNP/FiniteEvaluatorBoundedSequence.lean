import OAI.Computability.BorderVNP.FiniteEvaluatorCellsNative

/-! # Chronological field sums across a charged evaluator sequence

A returning prefix can spend different amounts of time on different private
choices. Each continuation uses the exact remaining tick budget and the bank
and shared memory returned by that particular prefix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamContraction
open scoped BigOperators Classical

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]

private theorem within_seq {es fs : List (TeamRAM.Event w)} {ticks burst clock : ℕ} :
    Within ticks burst clock (es++fs) ↔ Within ticks burst clock es ∧
      Within (ticks-traceCost es) burst clock fs := by
  have eq : traceCost (es++fs) = traceCost es+traceCost fs := VPVNP.RAMBuckets.cost_append ..
  constructor
  · intro h
    have ct : traceCost (es++fs) ≤ ticks := h.cost
    rw [eq] at ct
    exact ⟨⟨(Nat.le_add_right ..).trans ct,fun e he => h.length e (List.mem_append_left _ he),
      fun e he => h.choices e (List.mem_append_left _ he)⟩,
      ⟨by change traceCost fs ≤ _; omega,fun e he => h.length e (List.mem_append_right _ he),
        fun e he => h.choices e (List.mem_append_right _ he)⟩⟩
  · rintro ⟨a,b⟩
    have ac : traceCost es ≤ ticks := a.cost
    have bc : traceCost fs ≤ ticks-traceCost es := b.cost
    exact ⟨eq.trans_le (by omega),fun e he => (List.mem_append.mp he).elim (a.length e) (b.length e),
      fun e he => (List.mem_append.mp he).elim (a.choices e) (b.choices e)⟩

variable (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
variable (a b : Code) (s : Bank w) (mem : Memory w) (ticks burst clock : ℕ)

/-- Split a genuine bounded execution exactly at its native sequence boundary.
Both stages retain their true event choices and the same word and private caps. -/
noncomputable def chargedSeqEquiv (mac : TeamOpcode.Macros w 8) :
    (Σ x : Evaluator.BoundedReturns a pub mac s mem ticks burst clock,
      Evaluator.BoundedReturns b pub mac x.val.val.2.1 x.val.val.2.2 (ticks-traceCost x.val.val.1) burst clock) ≃
      Evaluator.BoundedReturns (.seq a b) pub mac s mem ticks burst clock := by
  let Raw := Σ x : Evaluator.Returns a pub mac s mem, Evaluator.Returns b pub mac x.val.2.1 x.val.2.2
  let both (z : Raw) := Within ticks burst clock z.1.val.1 ∧ Within (ticks-traceCost z.1.val.1) burst clock z.2.val.1
  let combine := Evaluator.seqReturnEquiv a b pub mac s mem
  let check := combine.subtypeEquiv (p := both) (q := fun z => Within ticks burst clock z.val.1) fun z =>
    (within_seq (es := z.1.val.1) (fs := z.2.val.1)).symm
  refine Equiv.trans ?_ check
  exact ⟨fun ⟨x,y⟩ => ⟨⟨x.val,y.val⟩,x.property,y.property⟩,
    fun z => ⟨⟨z.val.1,z.property.1⟩,⟨z.val.2,z.property.2⟩⟩,fun _ => rfl,fun _ => rfl⟩

/-- Native events of the full charged sequence are exactly those of the prefix
followed by the events from its true post-state. -/
theorem chargedSeqEquiv_events (mac : TeamOpcode.Macros w 8)
    (x : Evaluator.BoundedReturns a pub mac s mem ticks burst clock)
    (y : Evaluator.BoundedReturns b pub mac x.val.val.2.1 x.val.val.2.2 (ticks-traceCost x.val.val.1) burst clock) :
    (chargedSeqEquiv pub a b s mem ticks burst clock mac ⟨x,y⟩).val.val.1 = x.val.val.1++y.val.val.1 := rfl

/-- The exact bounded field sum for consecutive linked stages, including
arbitrary guessed prefixes and any resource cutoff that truncates a continuation. -/
theorem boundedWeight_seq (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ) :
    let mac := TeamSiteEvents.macros (w := w) lib fuel
    letI := Fintype.ofFinite (Evaluator.BoundedReturns a pub mac s mem ticks burst clock)
    boundedWeight pub lib ret fuel (.seq a b) s mem ticks burst clock =
      ∑ x : Evaluator.BoundedReturns a pub mac s mem ticks burst clock,
        weight pub lib ret fuel a s x.val.val.1 *
          boundedWeight pub lib ret fuel b x.val.val.2.1 x.val.val.2.2 (ticks-traceCost x.val.val.1) burst clock := by
  intro mac
  let A := Evaluator.BoundedReturns a pub mac s mem ticks burst clock
  let B (x : A) := Evaluator.BoundedReturns b pub mac x.val.val.2.1 x.val.val.2.2 (ticks-traceCost x.val.val.1) burst clock
  let := Fintype.ofFinite A
  let (x : A) := Fintype.ofFinite (B x)
  let := Fintype.ofFinite (Evaluator.BoundedReturns (.seq a b) pub mac s mem ticks burst clock)
  let E := chargedSeqEquiv pub a b s mem ticks burst clock mac
  unfold boundedWeight
  rw [← E.sum_comp (fun z => weight pub lib ret fuel (.seq a b) s z.val.val.1),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact weight_seq pub lib ret fuel x.val.property y.val.property

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
