import OAI.Computability.BorderVNP.PackedHistoryPinGeometry
import OAI.Computability.BorderVNP.DiagonalNativeValue

/-! # Chronological returns of the real pin and profile prefix

On an invalid broadcast the whole prefix has no return. For a valid broadcast every pin choice
has exactly one continuation through the geometry evaluator, with the stated words and time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA GeometryAdvice DiagonalResidueRAM
open RoutingISA.Evaluator

variable {w k o : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {mem : Memory w}

/-- The complete prefix on the evaluation branch after the common header is selected. -/
def pinGeometry : Code := .seq preparePins reconstruct

private theorem GeometryReturn.eq_return {fresh dest clock : ℕ} {out : Fin o → ℕ} {es after result}
    (h : GeometryReturn pub mac bank mem fresh dest clock out es after result)
    (y : Returns reconstruct pub mac bank mem) : y.val = (es,after,result) := by
  have he : y.val.1 = es := ((h.unique _ _).mp y.property.execute).1
  obtain ⟨_,hr,hm⟩ := y.property.eq_of_shared_events h.run (tail := []) (tail' := []) (by simpa using he)
  exact Prod.ext he (Prod.ext hr hm)

/-- Complete chronological equivalence through the pin-preparation and geometry stages, with
bit choices preserved and the unchanged-lower-memory property measured relative to the pin
memory for the same real private choice. -/
theorem pinGeometry_paths (pins : (Fin k → Bool) ≃ Pins.Return pub mac bank mem)
    (ok : Prop) (fresh dest pinTime clock : ℕ) (out : Fin o → ℕ)
    (steps : ∀ g, let h := pins g
      h.val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost h.val.1 ≤ pinTime ∧
      ((∃ es choices, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,h.val.2.1⟩ h.val.2.2 choices = some es) ↔ ok) ∧
      (ok → ∃ es after result, GeometryReturn pub mac h.val.2.1 h.val.2.2 fresh dest clock out es after result)) :
    (Nonempty (Returns pinGeometry pub mac bank mem) ↔ ok) ∧
      (ok → ∃ E : (Fin k → Bool) ≃ Returns pinGeometry pub mac bank mem, ∀ g,
        (E g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (E g).val.1 ≤ pinTime+clock ∧
        signedWeight (E g).val.1 = 1 ∧ (∀ i, readings (E g).val.2.2 (dest+i.val) = out i) ∧
        ∀ a < fresh, (E g).val.2.2 a = (pins g).val.2.2 a) := by
  classical
  let split := seqReturnEquiv preparePins reconstruct pub mac bank mem
  have accepted (y : Returns pinGeometry pub mac bank mem) : ok := by
    let z := split.symm y
    let g := pins.symm z.1
    have eq : pins g = z.1 := pins.apply_symm_apply _
    have test := (steps g).2.2.1
    rw [eq] at test
    exact test.mp ⟨z.2.val.1,_,z.2.property.execute⟩
  have build (pass : ok) : ∃ E : (Fin k → Bool) ≃ Returns pinGeometry pub mac bank mem, ∀ g,
        (E g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost (E g).val.1 ≤ pinTime+clock ∧
        signedWeight (E g).val.1 = 1 ∧ (∀ i, readings (E g).val.2.2 (dest+i.val) = out i) ∧
        ∀ a < fresh, (E g).val.2.2 a = (pins g).val.2.2 a := by
    choose es b m h using fun g => (steps g).2.2.2 pass
    let extend (g : Fin k → Bool) : Returns pinGeometry pub mac bank mem :=
      split ⟨pins g,⟨(es g,b g,m g),(h g).run⟩⟩
    have inj : Function.Injective extend := by
      intro g j eq
      apply pins.injective
      exact congrArg Sigma.fst (split.injective eq)
    have sur : Function.Surjective extend := by
      intro y
      obtain ⟨⟨p,y'⟩,rfl⟩ := split.surjective y
      obtain ⟨g,rfl⟩ := pins.surjective p
      exact ⟨g,congrArg (fun u => split ⟨pins g,u⟩) (Subtype.ext ((h g).eq_return y').symm)⟩
    refine ⟨Equiv.ofBijective extend ⟨inj,sur⟩,fun g => ?_⟩
    have effect := (h g).effects
    have pp := Pins.preparePins_positive (pins g).property
    have plus : signedWeight (pins g).val.1 = 1 := by
      apply List.prod_eq_one
      simp only [List.mem_map]
      rintro _ ⟨a,ha,rfl⟩; simp [pp a ha,TeamRAM.Sign.value]
    change ((pins g).val.1++es g).flatMap TeamRAM.Event.choices = _ ∧ traceCost ((pins g).val.1++es g) ≤ _ ∧
      signedWeight ((pins g).val.1++es g) = 1 ∧ _
    rw [List.flatMap_append,(steps g).1,effect.2.2,List.append_nil,show traceCost ((pins g).val.1++es g) = _ from VPVNP.RAMBuckets.cost_append ..]
    refine ⟨rfl,Nat.add_le_add (steps g).2.1 (h g).time,?_,(h g).words,(h g).preserved⟩
    simpa only [signedWeight,List.map_append,List.prod_append,one_mul] using congrArg₂ (·*·) plus effect.2.1
  exact ⟨⟨fun ⟨y⟩ => accepted y,fun pass => ⟨(build pass).choose (fun _ => false)⟩⟩,build⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
