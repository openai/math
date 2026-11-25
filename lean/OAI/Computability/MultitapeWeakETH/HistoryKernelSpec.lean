import OAI.Computability.MultitapeWeakETH.ShrinkKernelReader
import OAI.Computability.VPVNP.PairRefreshTraversalOriginBits
import OAI.Computability.VPVNP.PairRefreshTraversalWitness

/-! # Private words and global exponents of the two scheduled kernel readers -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif CompressorRecords NetworkKernel
open Compression.DegreeRefresh Compression.Refresh PairSimulation LocalHistory PortRefresh RefreshMapOperands
open ShrinkMap
open PortRefresh.TraversalPlan
open scoped Classical Fin.CommRing
noncomputable section

/-- One fixed list of global coefficient ordinals per local choice. The reader
consumes its scheduled code and returns the exact remaining private suffix. -/
def KernelSpec {L X : Type} {hist : ℕ} (order : L ≃ Fin hist) (encode : X → Bits.Word)
    (exponents : X → L → ℕ) (run : Bits.Word → Option (List Tally × Bits.Word)) : Prop :=
  ∃ names : X → List (Fin hist), (∀ x l, (names x).count (order l) = exponents x l) ∧
    ∀ bits labels tail, run bits = some (labels,tail) ↔
      ∃ x, bits = encode x ++ tail ∧ labels = (names x).map (tally ∘ Fin.val)

private theorem fixedEmission {X L : Type} {hist : ℕ} (order : L ≃ Fin hist)
    (enc : X → Bits.Word) (exps : X → L → ℕ) (em : Option (List (Fin hist)))
    (present : em.isSome = true ↔ Nonempty X) (empty : ∀ x, enc x = [])
    (counts : ∀ x l, (em.getD []).count (order l) = exps x l) :
    KernelSpec order enc exps (fun bits => (em.map (List.map (tally ∘ Fin.val))).bind fun ls => some (ls,bits)) := by
  refine ⟨fun _ => em.getD [],counts,?_⟩
  intro bits labels tail
  cases em with
  | none =>
    constructor
    · intro h; cases h
    · rintro ⟨x,_⟩; exact Bool.noConfusion (present.mpr ⟨x⟩)
  | some ls =>
    obtain ⟨x⟩ := present.mp rfl
    simp only [Option.map_some,Option.bind_some,Option.some.injEq,Prod.mk.injEq,empty,List.nil_append,Option.getD_some]
    exact ⟨fun ⟨names,word⟩ => ⟨x,word,names.symm⟩,fun ⟨_,word,names⟩ => ⟨names.symm,word⟩⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] ShrinkEnergy.chosenLayout
variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → R) (hf : B.IsSolution f)
    {i : Fin S.steps} {g : ℕ} (z : SiteArguments B i g)

local notation "W" => B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent
local notation "emittedAt" => ShrinkRole.MapWitness.emitted B f hf i z.state z.choice z.owner z.old z.parent
set_option quotPrecheck false in
local notation "scheduled" => (shrinkPassReaders B f hf i rfl z.state).termParsers z.choice

set_option maxHeartbeats 1600000 in
theorem shrink_kernel_spec (run : Bits.Word → Option (List Tally × Bits.Word))
    (check : ∀ bits labels tail, run bits = some (labels,tail) ↔ ∃ x : (W).Choice,
      bits = ShrinkHiddenGuess.stream (hiddenRows z x.1) ++ tail ∧
      labels = (emittedAt x).map (tally ∘ (fun l => (order (.inl l)).val))) :
    KernelSpec order ((scheduled).read z.owner z.old z.parent).encode (W).exponents run := by
  let names (x : (W).Choice) := (emittedAt x).map (order ∘ Sum.inl)
  refine ⟨names,?_,?_⟩
  · intro x l
    cases l with
    | inl l =>
      exact (List.count_map_of_injective _ (order ∘ Sum.inl) (order.injective.comp Sum.inl_injective) l).trans
        (ShrinkRole.MapWitness.emitted_count B f hf i z.state z.choice z.owner z.old z.parent x l)
    | inr l =>
      change (names x).count (order (.inr l)) = 0
      apply List.count_eq_zero.mpr
      intro mem
      obtain ⟨q,_,same⟩ := List.mem_map.mp mem
      exact Sum.inl_ne_inr (order.injective same)
  · intro bits labels tail
    refine (check bits labels tail).trans (exists_congr fun x => ?_)
    have code := ShrinkHiddenSlots.kernel_encode B f hf i z.state z.choice z.owner z.old z.parent x
    have same : ShrinkHiddenGuess.stream (hiddenRows z x.1) =
        ((scheduled).read z.owner z.old z.parent).encode x := by
      dsimp +instances only [ShrinkHiddenGuess.stream,List.flatMap_def,hiddenRows,SelectedFinish.chosen,
        ShrinkPreparedCall.width,PassReaders.termParsers] at ⊢
      exact code.symm
    apply and_congr
    · exact (congrArg (fun bs => bits = bs ++ tail) same).to_iff
    · simp only [names,List.map_map,Function.comp_def]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
