import OAI.Computability.BorderVNP.FiniteEvaluatorSequence

/-! # The fetched field factors of a single-routine evaluator stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA FieldProcessor TeamRAM

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]

/-- The field factor of one native event when all private instructions in the
stage call the indicated routine. Every ordinary event retains its own sign. -/
noncomputable def atID (j : Macro) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m 8)
    (fuel : ℕ) (e : TeamRAM.Event w) : F :=
  if burst e then (returned (lib j) (ret j) fuel e).getD 0 else (e.sign.value : F)

/-- Read every native field factor from the true routine, whose identity is
verified from the actual compiled control flow of the stage. -/
theorem weight_atID (j : Macro) (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m 8)
    (fuel : ℕ) {c s mem es z mz} (run : Runs pub (TeamSiteEvents.macros lib fuel) c s mem es z mz)
    (only : ∀ i, uses i c = true → i=j) :
    weight pub lib ret fuel c s es = (es.map (atID j lib ret fuel)).prod := by
  obtain ⟨xs,hx⟩ := spelling run
  have own := hx.linked c (label c) 0 c.slots (selfContains c)
  rw [show label c 0 = 0 by ext; simp [label]] at own
  have h := DiagonalResidueRAM.at_last run
  have agree := trace_bursts h
  have events := trace_events h
  rw [own] at agree events
  rw [weight,trace_value lib ret fuel h,own,← events,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨id,e⟩ he
  have hb := agree _ he
  cases id with
  | none =>
    change false = burst e at hb
    simp [atID,value,hb.symm]
  | some i =>
    have id := only i (hx.ids i e he)
    change true = burst e at hb
    simp [atID,value,id,hb.symm]

/-- When all ordinary operations are positive, the product is the product of the
true private returns, including private calls with zero input words. -/
theorem positive_weight (j : Macro) (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g)
    (ret : Returns Q Γ F m 8) (fuel : ℕ) {c s mem es z mz}
    (run : Runs pub (TeamSiteEvents.macros lib fuel) c s mem es z mz)
    (only : ∀ i, uses i c = true → i=j) (clean : ∀ e ∈ es, e.sign = .plus) :
    weight pub lib ret fuel c s es = ((es.filter burst).map (fun e => (returned (lib j) (ret j) fuel e).getD 0)).prod := by
  rw [weight_atID j pub lib ret fuel run only]
  clear run only
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hp := clean e List.mem_cons_self
    have rest := ih (fun v hv => clean v (List.mem_cons_of_mem _ hv))
    cases hb : burst e <;> simp [hb,atID,hp,Sign.value,rest]

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
