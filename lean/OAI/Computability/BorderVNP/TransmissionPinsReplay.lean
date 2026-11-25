import OAI.Computability.BorderVNP.TransmissionPins
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-!
# Exact multiplicity of a fixed-length pin guess

The original native fetch semantics determines the full chronological trace from a stream
of guesses. Padding a returned stream is used only in this proof, to show that prescribed
fixed-length executions exhaust every possible successful return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w k : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
  {s : Bank w} {m : Memory w}

/-- One possible return of the preparation code, recording the whole trace and both
the actual final register bank and the actual final memory. -/
def Return (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  {z : List (TeamRAM.Event w) × Bank w × Memory w // Runs pub macros preparePins s m z.1 z.2.1 z.2.2}

/-- Two returns of pin preparation on compatible complete guess streams coincide, including
all accesses, words and the final bank. -/
theorem return_eq_of_stream {a b : Return pub macros s m} {u v : List Bool}
    (h : a.val.1.flatMap TeamRAM.Event.choices ++ u = b.val.1.flatMap TeamRAM.Event.choices ++ v) :
    a = b := by
  obtain ⟨he,hr,hm⟩ := DiagonalResidueRAM.unique_returns (c := preparePins)
    (by decide) a.property b.property h
  exact Subtype.ext (Prod.ext he (Prod.ext hr hm))

/-- Every return of the actual native pin preparation is represented by the fixed
number of guessed bits, provided one returning execution has been constructed for
each of these bit assignments. Its effects and trace are uniquely determined. -/
noncomputable def returnEquiv (run : (Fin k → Bool) → Return pub macros s m)
    (bits : ∀ b, (run b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b) :
    (Fin k → Bool) ≃ Return pub macros s m := Equiv.ofBijective run (by
  constructor
  · intro a b he
    exact List.ofFn_injective ((bits a).symm.trans (he ▸ bits b))
  · intro z
    let stream := z.val.1.flatMap TeamRAM.Event.choices ++ List.replicate k false
    have hk : k ≤ stream.length := by simp [stream]
    let b (i : Fin k) := stream[i.val]'(i.isLt.trans_le hk)
    have cut : List.ofFn b = stream.take k := by
      apply List.ext_getElem (by simp [hk])
      intro i _ _
      simp [b]
    have shared : (run b).val.1.flatMap TeamRAM.Event.choices ++ stream.drop k =
        z.val.1.flatMap TeamRAM.Event.choices ++ List.replicate k false := by
      rw [bits, cut, List.take_append_drop]
    exact ⟨b, return_eq_of_stream shared⟩)

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
