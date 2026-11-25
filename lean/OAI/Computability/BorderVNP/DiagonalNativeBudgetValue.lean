import OAI.Computability.BorderVNP.DiagonalNativeEvalStartup

/-! # The charged signed value of an evaluator continuation

The finite enumeration uses the actual chronological private choice blocks. It works
on a post-prefix RAM image, including all writes already made by the startup table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction Pins
open scoped BigOperators Classical
open private Tapes tapesFinite from OAI.Computability.BorderVNP.TeamContractionPaths

variable {w : ℕ}

/-- Returning native histories satisfying all three paper resource cutoffs on the current RAM image. -/
abbrev BoundedReturns (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ticks burst clock : ℕ) := {p : Returns c pub mac s m // Within ticks burst clock p.val.1}

/-- On any actual RAM image, the exact chronological choice blocks uniquely identify
every bounded return, including its final registers and memory. -/
instance finiteBoundedReturns (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ticks burst clock : ℕ) : Finite (BoundedReturns c pub mac s m ticks burst clock) := by
  let := tapesFinite ticks clock
  let key (x : BoundedReturns c pub mac s m ticks burst clock) : Tapes ticks clock :=
    ⟨x.val.val.1.map TeamRAM.Event.choices, by
      constructor
      · rw [List.length_map]
        have h := x.property.cost
        rw [RAMBuckets.cost_eq_length_add_probes] at h
        omega
      · intro b hb
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
        exact x.property.choices e he⟩
  apply Finite.of_injective key
  intro a b he
  have tapes : a.val.val.1.map TeamRAM.Event.choices = b.val.val.1.map TeamRAM.Event.choices := congrArg Subtype.val he
  have hr := a.val.property.execute
  rw [tapes,b.val.property.execute] at hr
  have same := (Option.some.inj hr).symm
  obtain ⟨_,ht,hm⟩ := a.val.property.eq_of_shared_events b.val.property (congrArg (· ++ []) same)
  exact Subtype.ext (Subtype.ext (Prod.ext same (Prod.ext ht hm)))

/-- Actual signed continuation value at a specified tick, burst and private-choice cutoff. -/
noncomputable def boundedValue (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ticks burst clock : ℕ) : ℤ :=
  letI := Fintype.ofFinite (BoundedReturns c pub mac s m ticks burst clock)
  ∑ p : BoundedReturns c pub mac s m ticks burst clock, pathWeight p.val.val.1

/-- Removing startup and common-tag dispatch from the fully charged initialized machine
leaves precisely the selected body's signed value at the remaining instruction budget. -/
theorem startup_selected_value (f : BroadcastFrame) (eval : Code) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {L : Layout} (fields : ProcessorFields L) (s : Bank w)
    {pre u mu hs b mb} (start : Runs pub mac unitStartup s (processorMemory fields w) pre u mu)
    (header : Runs pub mac readBroadcast u mu hs b mb) (stable : f.Stable (readings b))
    (he : eval.withoutAccept = true) (ticks burst clock : ℕ) (fit : pre.length+hs.length+2 ≤ ticks) :
    nativeValue (processorMachine (withStartup eval) pub mac s fields) ticks burst clock =
      boundedValue (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb
        (ticks-(pre.length+hs.length+2)) burst clock := by
  let := Fintype.ofFinite (BoundedReturns (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb
    (ticks-(pre.length+hs.length+2)) burst clock)
  let := Fintype.ofFinite (NativePath (processorMachine (withStartup eval) pub mac s fields) ticks burst clock)
  let E := chargedStartupEquiv f eval start header stable fields rfl he ticks burst clock fit
  change (∑ p : NativePath _ ticks burst clock, pathWeight p.val) = ∑ p : BoundedReturns _ _ _ _ _ _ _ _, pathWeight p.val.val.1
  rw [← E.sum_comp (fun z => pathWeight z.val)]
  apply Finset.sum_congr rfl
  intro x _
  have events : (E x).val = dispatchPrefix f mb pre hs ++ x.val.val.1 :=
    congrArg Prod.fst (startupReturnEquiv_val f eval start header stable x.val)
  have pos := (dispatchPrefix_effects f start header).2
  rw [events]
  simp only [pathWeight,List.map_append,List.prod_append] at pos ⊢
  rw [pos,one_mul]

/-- If all real continuations meet their remaining resource allowances, the bounded
value is the signed sum over every native return. -/
theorem boundedValue_eq_sum (c : Code) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ticks burst clock : ℕ) (budget : ∀ z : Returns c pub mac s m, Within ticks burst clock z.val.1)
    [Fintype (Returns c pub mac s m)] :
    boundedValue c pub mac s m ticks burst clock = ∑ z : Returns c pub mac s m, pathWeight z.val.1 := by
  let := Fintype.ofFinite (BoundedReturns c pub mac s m ticks burst clock)
  let E : Returns c pub mac s m ≃ BoundedReturns c pub mac s m ticks burst clock :=
    ⟨fun z => ⟨z,budget z⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact (E.sum_comp (fun z => pathWeight z.val.val.1)).symm

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
