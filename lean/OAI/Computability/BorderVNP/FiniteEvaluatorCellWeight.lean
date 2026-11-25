import OAI.Computability.BorderVNP.FiniteEvaluatorSigned
import OAI.Computability.BorderVNP.RoutingISAFiniteScalarPhysical
import OAI.Computability.BorderVNP.DiagonalNativeSiteMacro
import OAI.Computability.BorderVNP.RoutingISATypedNativeValue

/-! # Actual signed-cell and field-scalar weights in the emitted team program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM FieldProcessor FiniteScalarLibrary

variable {w p r k a m g : ℕ} {Q Γ : Type} {F : Type*} [Field F] [Fintype F]

/-- A real private mark was admitted at that exact identifier with the stated old
words, complete private choices and the sign recorded by the RAM. -/
theorem trace_valid {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w} {mac : TeamOpcode.Macros w a}
    {s mem es z mz} (h : NativePrefix (P.fetch pub mac) s mem es z mz) :
    ∀ j e, (some j,e) ∈ trace P pub mac s es → mac j e.old e.choices = some e.sign := by
  induction h with
  | nil => simp [trace]
  | @cons s mem act bs next sg rest z mz action step _ ih =>
    rw [trace,step]
    intro j e he
    rcases List.mem_cons.mp he with he | he
    · obtain ⟨id,rfl⟩ := Prod.mk.inj he
      rw [← TeamOpcode.prepare_action] at step
      cases tag : (TeamOpcode.prepare P pub s).1 with
      | native | sign => rw [tag] at id; contradiction
      | call i addr len pc =>
        rw [tag] at id step
        have e : j=i := Option.some.inj id
        subst j
        simp only [TeamOpcode.Exit.action,Instr.advance] at step
        split at step <;> try contradiction
        obtain ⟨z,hz,heq⟩ := Option.map_eq_some_iff.mp step
        exact hz.trans (congrArg some (congrArg Prod.snd heq))
    · exact ih j e he

/-- On a stage that never fetches the new scalar opcode, the actual combined
processor returns the original signed history interpreted in the finite field. -/
theorem old_weight (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (fuel : ℕ) {c s mem es z mz} (run : Runs pub (TeamSiteEvents.macros (combine F lib) fuel) c s mem es z mz)
    (old : uses 1 c = false) :
    weight pub (combine F lib) (returns F lib (fun _ => signedReturn)) fuel c s es = (TeamContraction.pathWeight es : F) := by
  obtain ⟨xs,hx⟩ := spelling run
  have own := hx.linked c (label c) 0 c.slots (selfContains c)
  rw [show label c 0 = 0 by ext; simp [label]] at own
  have prefixRun := DiagonalResidueRAM.at_last run
  have good := trace_valid prefixRun
  have events := trace_events prefixRun
  rw [own] at good events
  rw [weight,trace_value _ _ _ prefixRun,own,← events,TeamContraction.pathWeight,Int.cast_list_prod,List.map_map,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨id,e⟩ he
  cases id with
  | none => rfl
  | some j =>
    have hj : j≠1 := by rintro rfl; have := hx.ids 1 e he; rw [old] at this; contradiction
    exact combined_signed lib fuel j hj e (good j e he)

/-- All scalar-stage bursts really fetch slot one and multiply precisely the
reported field return list. The comparison of marked lists includes length-zero
private reads and the deterministic packing and address instructions. -/
theorem scalar_weight (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (old : Returns Q (Option Bool) F m 8) (fuel : ℕ) {s mem es z mz}
    (run : Runs pub (TeamSiteEvents.macros (combine F lib) fuel) FiniteScalarBatch.code s mem es z mz)
    (reported : List F)
    (reads : (FiniteScalarBatch.bursts es).map (returned (combine F lib 1) (returns F lib old 1) fuel) = reported.map some)
    (clean : ∀ e ∈ es, e.sign=.plus) :
    weight pub (combine F lib) (returns F lib old) fuel FiniteScalarBatch.code s es = reported.prod := by
  have id : ∀ i, uses i FiniteScalarBatch.code=true → i=1 := by decide
  rw [positive_weight 1 pub _ _ fuel run id clean]
  have flags : (burst (w := w)) = FiniteScalarBatch.isBurst := by
    funext e; rcases e with ⟨act,old,bits,sg⟩; cases act <;> rfl
  rw [flags]
  have factors := congrArg (List.map (fun x : Option F => x.getD 0)) reads
  apply congrArg List.prod
  simp only [FiniteScalarBatch.bursts,List.map_map,Function.comp_def,Option.getD_some] at factors
  exact factors.trans (List.map_id reported)

/-- The concrete validator and scalar stage coexist in the actual literal library.
Every compiled native path has exactly the original signed validator weight
multiplied by the genuine field returns of its own scalar suffix. -/
theorem cells_weight (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (fuel : ℕ) {s mem es t mt fs z mz}
    (validator : Runs pub (TeamSiteEvents.macros (combine F lib) fuel) TypedBatch.runCells s mem es t mt)
    (scalar : Runs pub (TeamSiteEvents.macros (combine F lib) fuel) FiniteScalarBatch.code t mt fs z mz)
    (reported : List F)
    (reads : (FiniteScalarBatch.bursts fs).map (returned (combine F lib 1) (returns F lib (fun _ => signedReturn) 1) fuel) = reported.map some)
    (clean : ∀ e ∈ fs, e.sign=.plus) :
    weight pub (combine F lib) (returns F lib (fun _ => signedReturn)) fuel (.seq TypedBatch.runCells FiniteScalarBatch.code) s (es++fs) =
      (TeamContraction.pathWeight es : F) * reported.prod := by
  rw [weight_seq pub _ _ fuel validator scalar,old_weight pub lib fuel validator (by decide),
    scalar_weight pub lib _ fuel scalar reported reads clean]

/-- Installing the concrete sparse validator in its literal slot zero still
agrees with the combined field library at every runtime identifier. -/
theorem install_combined (F : Type*) [Field F] [Fintype F] (gen : CellMacro.Generator.Fragment CellMacro.Generator.IO) (n : ℕ) :
    let lib := combine F (CompactMachine.siteLibrary gen)
    let mac := TeamSiteEvents.macros (w := w) lib (CompactMachine.nativeClock n)
    CompactMachine.install gen n mac = mac := by
  intro lib mac
  funext j
  by_cases hj : j=0
  · subst j
    rw [CompactMachine.install,Function.update_self]
    funext vs bs
    change _ = (combine F (CompactMachine.siteLibrary gen) 0).eval (CompactMachine.nativeClock n) vs bs
    rw [original_eval _ _ _ (by decide)]
    exact (CompactMachine.siteMacro_eval gen n vs bs).symm
  · rw [CompactMachine.install,Function.update_of_ne hj]

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
