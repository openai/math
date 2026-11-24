import OAI.Computability.VPVNP.SlotPacking

/-!
# Directed incidences at the thin endpoint

Appendix C assigns each non-thick–thick wire to the bundle of its thin
endpoint C. The original direction breaks ties on thin–thin wires. Incoming
wires can be enumerated at their target through the inverse slot permutation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- Partition the actual CD wires by their old direction relative to C.
The predicate may inspect either old position. This allows the same
enumeration to count demands by bundle or by the new position of D. -/
def cdIncidenceEquiv (p : Position V H Tag L c → Position V H Tag L c → Prop) :
    {m : P.Motif // p (P.C m) (P.D m)} ≃
    {a : Arc V H Tag L d c // ¬ P.thick (sourcePosition a) ∧
      p (sourcePosition a) (sourcePosition (P.actual a))} ⊕
    {a : Arc V H Tag L d c // P.thick (sourcePosition (P.actual.symm a)) ∧
      ¬ P.thick (sourcePosition a) ∧ p (sourcePosition a) (sourcePosition (P.actual.symm a))} where
  toFun m :=
    if hs : P.thick (sourcePosition m.1.1) then
      Sum.inr ⟨P.actual m.1.1, by
        simp only [Equiv.symm_apply_apply]
        exact ⟨hs, fun ht ↦ m.1.2 ⟨hs, ht⟩, by simpa [C, D, hs] using m.2⟩⟩
    else Sum.inl ⟨m.1.1, hs, by simpa [C, D, hs] using m.2⟩
  invFun
    | .inl a => ⟨⟨a.1, fun h ↦ a.2.1 h.1⟩, by simpa [C, D, a.2.1] using a.2.2⟩
    | .inr a => ⟨⟨P.actual.symm a.1, fun h ↦ a.2.2.1 (by simpa using h.2)⟩, by
        simpa [C, D, a.2.1] using a.2.2.2⟩
  left_inv m := by
    by_cases hs : P.thick (sourcePosition m.1.1) <;> simp [hs]
  right_inv a := by
    rcases a with a | a
    · simp [a.2.1]
    · simp [a.2.1]

end Compression.PackingData

end VPVNP
end Computability
end OAI
