import OAI.Computability.BorderVNP.ParseBooleanPhysical
import OAI.Computability.BorderVNP.TransmissionInputParser
import OAI.Computability.BorderVNP.TeamContractionWireScale

/-! # Prewiring a team's query inputs before placing any of its vertices

The visible prefix is the literal, partner-ordered exterior and reserved pin
fields. Each following interior slot either reads its shared private variable
or is clamped to zero. Trailing padding is a constant in the Boolean verifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.Prewire

open VPVNP BooleanTranscript TeamContraction
open scoped Classical

variable {R r t d link inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

/-- Number of public positions per processor in literal, exterior, pin order. -/
def publicWidth := 2*(G.program.length+t) + R*link

/-- Variable or zero-clamp assigned to every original query input before
fanout is built. The public ordinal is processor-major then field-major. -/
def source (j : Fin r) (i : Fin n) : ((Fin r × Fin (publicWidth G)) ⊕ Edge) ⊕ Bool :=
  if hv : i.val < publicWidth G then .inl (.inl (j,⟨i.val,hv⟩))
  else if hi : i.val-publicWidth G < inner then
    (G.interior j ⟨i.val-publicWidth G,hi⟩).elim (.inr false) (.inl ∘ .inr)
  else .inr false

/-- The visible values of the actual physical team, including the designated pin bits. -/
def publicBits (team : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (u : Fin r × Fin (publicWidth G)) : Bool :=
  ((G.processorFields team pin ext 0 0 0).row u.1)[u.2.val]'(by
    rw [(G.processorFields team pin ext 0 0 0).row_length u.1]
    simpa [publicWidth,Wiring.pinLayout,RoutingISA.Pins.Layout.stride,RoutingISA.Pins.Layout.offset,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm, two_mul] using u.2.isLt)

/-- The rewired Boolean input recovers the signed processor word on every
combination of actual private links, global exterior links and pin. -/
theorem source_read (team : Fin (R+1)) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (privateBits : Edge → Bool) (j : Fin r) (i : Fin n) :
    (source G j i).elim (Sum.elim (publicBits G team pin ext) privateBits) id =
      G.word pin ext privateBits team j i := by
  let row := (G.processorFields team pin ext 0 0 0).row j
  have len : row.length = publicWidth G := by
    change ((G.processorFields team pin ext 0 0 0).row j).length = _
    rw [(G.processorFields team pin ext 0 0 0).row_length j]
    simp [publicWidth,Wiring.pinLayout,RoutingISA.Pins.Layout.stride,RoutingISA.Pins.Layout.offset]
    omega
  have h := G.word_processorFields team j pin ext privateBits 0 0 0
  change List.ofFn (G.word pin ext privateBits team j) = row ++ _ ++ _ at h
  have hi := congrArg (fun l : List Bool => l[i.val]?) h
  rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn] at hi
  change some (G.word pin ext privateBits team j i) = _ at hi
  by_cases hv : i.val < publicWidth G
  · simp only [source, dite_eq_left hv, Sum.elim_inl, publicBits]
    rw [List.getElem?_append_left (by simp only [List.length_append, len, List.length_ofFn]; omega),
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)] at hi
    exact (Option.some.inj hi).symm
  · by_cases he : i.val-publicWidth G < inner
    · simp only [source, dite_eq_right hv, dite_eq_left he]
      rw [List.getElem?_append_left (by simp only [List.length_append, len, List.length_ofFn]; omega),
        List.getElem?_append_right (by omega), len, List.getElem?_eq_getElem (by simpa using he),
        List.getElem_ofFn] at hi
      cases heq : G.interior j ⟨i.val-publicWidth G,he⟩ <;> simpa [heq] using (Option.some.inj hi).symm
    · simp only [source, dite_eq_right hv, dite_eq_right he, Sum.elim_inr, id_eq]
      rw [List.getElem?_append_right (by simp only [List.length_append, len, List.length_ofFn]; omega),
        List.length_append, len, List.length_ofFn, List.getElem?_eq_getElem (by
          simp only [List.length_replicate]
          change i.val - (publicWidth G+inner) < n-(publicWidth G+inner)
          have := i.isLt; omega), List.getElem_replicate] at hi
      exact (Option.some.inj hi).symm

variable {X Y W I : Type} {s : ℕ}

/-- Substitute variables or Boolean constants directly at the operands. No
gate is added, including when many processor inputs use the same interior wire. -/
def gates (f : Projection Bool X Y) : {s : ℕ} → BooleanTranscript.Program X s → BooleanTranscript.Program Y s
  | _, .nil => .nil
  | _, .snoc p (.and a b) => .snoc (gates f p) (.and (a.subst f id) (b.subst f id))
  | _, .snoc p (.not a) => .snoc (gates f p) (.not (a.subst f id))

/-- Rewire the designated result by the same input substitution as the gates. -/
def circuit (f : Projection Bool X Y) (c : BooleanTranscript.Circuit X s) : BooleanTranscript.Circuit Y s :=
  ⟨gates f c.program,c.output.subst f id⟩

private theorem read_ref (f : Projection Bool X Y) (a : Y → Bool) (w : Fin s → Bool) (v : Ref Bool X s) :
    (v.subst f id).read id a w = v.read id (fun i => (f i).elim a id) w := by
  cases v with
  | var i => cases h : f i <;> simp [Ref.read,Ref.subst,h]
  | const | gate => rfl

private theorem run_gates (f : Projection Bool X Y) (p : BooleanTranscript.Program X s) (a : Y → Bool) :
    (gates f p).run a = p.run (fun i => (f i).elim a id) := by
  induction p with
  | nil => rfl
  | snoc p g ih => cases g <;> simp [gates, BooleanTranscript.Program.run, BooleanTranscript.Gate.eval, ih, read_ref]

/-- Evaluation of the physical gate table uses the actual substituted bits. -/
theorem circuit_eval (f : Projection Bool X Y) (c : BooleanTranscript.Circuit X s) (a : Y → Bool) :
    (circuit f c).eval a = c.eval (fun i => (f i).elim a id) := by
  simp [circuit,BooleanTranscript.Circuit.eval,run_gates,read_ref]

/-- Move every interior wire to the private side of the verifier while keeping
each original parse and histogram guess independently named. -/
def projection (f : X → (Y ⊕ I) ⊕ Bool) : Projection Bool (X ⊕ W) (Y ⊕ (I ⊕ W))
  | .inr w => .inl (.inr (.inr w))
  | .inl x => (f x).elim (fun yi => .inl (yi.map id Sum.inl)) Sum.inr

end ParseBatch.Prewire

end BorderVNP
end Computability
end OAI
