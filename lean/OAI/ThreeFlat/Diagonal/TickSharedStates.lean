import OAI.ThreeFlat.Diagonal.SharedHistoryRegister
import OAI.ThreeFlat.Diagonal.TickAuxProjection

namespace OAI
/-! # Physical opening and closing indices for canonical, shared histories -/

noncomputable section
namespace ThreeFlat.Diagonal.TickAuxiliary

open TickChronology HistoryContraction

variable {F : Type*} [CommSemiring F] {S : Shape} {a : ℕ}
variable (P : Plan F S) (E : P.Codes) (bits : P.History → ℕ) (L : Layout a)
    (room : ∀ h, (P.write E h).length + bits h ≤ L.wiresEnd-1)

private def field (v : Plan.Terminal P bits) : Fin (L.wiresEnd-1) → Bool :=
  let s := Plan.encodeShared P E bits (L.wiresEnd-1) v
  fun i => s.get (i.cast (Plan.encodeShared_length P E bits _ v (room v.1)).symm)

private theorem list_field (v : Plan.Terminal P bits) :
    List.ofFn (field P E bits L room v) = Plan.encodeShared P E bits (L.wiresEnd-1) v := by
  let s := Plan.encodeShared P E bits (L.wiresEnd-1) v
  have len : s.length = L.wiresEnd-1 := Plan.encodeShared_length P E bits _ v (room v.1)
  suffices hx : ∀ (l : List Bool) (n : ℕ) (hl : l.length = n),
      List.ofFn (fun i : Fin n => l.get (i.cast hl.symm)) = l by
    exact hx s _ len
  rintro l _ rfl
  exact List.ofFn_get l

/-- The physical word at any boundary between groups. No pair has been
proposed, and all unoccupied positions are prescribed zero. -/
def boundary (v : Plan.Terminal P bits) : Fin a → Bool :=
  pack L ⟨true,field P E bits L room v,fun _ => false,fun _ => false⟩

def decode (v : Fin a → Bool) :=
  Plan.decodeShared P E bits (L.wiresEnd-1) (List.ofFn (project L v).history)

@[simp] theorem decode_boundary (v : Plan.Terminal P bits) :
    decode P E bits L (boundary P E bits L room v) = some v := by
  simp [decode,boundary,project_pack,list_field,Plan.decode_encode]

theorem boundary_injective : Function.Injective (boundary P E bits L room) := by
  intro v v' h
  simpa only [decode_boundary,Option.some.injEq] using congrArg (decode P E bits L) h

private theorem field_of_decode {x : Fin a → Bool} {v : Plan.Terminal P bits}
    (ok : decode P E bits L x = some v) :
    field P E bits L room v = (project L x).history := by
  apply List.ofFn_inj.mp
  rw [list_field]
  exact Plan.encode_decode P E bits _ _ v ok

/-- The accepted physical opening is precisely the selected canonical terminal
history and final wires, with empty group-pair storage. -/
theorem opening {x : Fin a → Bool} {v : Plan.Terminal P bits} :
    L.accepts .opening true (fun _ => false) x ∧ decode P E bits L x = some v ↔
      x = boundary P E bits L room v := by
  constructor
  · rintro ⟨h,ok⟩
    obtain ⟨_,pad,_,mk,_,_,pair⟩ := (accepts_phase L .opening _ _).mp h
    have hh := field_of_decode P E bits L room ok
    apply (auxEquiv L).injective
    change project L x = project L (pack L _)
    rw [project_pack]
    cases hx : project L x with
    | mk z hist p b =>
      rw [hx] at mk pair pad hh
      simp_all
  · rintro rfl
    refine ⟨?_,decode_boundary ..⟩
    rw [accepts_phase, boundary, project_pack]
    simp [phaseFields, project]

/-- The closing test is the transpose of the opening on the history branch. -/
theorem closing (x : Fin a → Bool) :
    L.accepts .closing true x (fun _ => false) ↔ L.accepts .opening true (fun _ => false) x := by
  rw [accepts_phase,accepts_phase]
  simp [phaseFields,project,and_comm,and_left_comm]

end ThreeFlat.Diagonal.TickAuxiliary

end
end OAI
