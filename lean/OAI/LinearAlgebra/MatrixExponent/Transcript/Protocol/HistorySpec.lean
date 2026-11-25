import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.OrderSpec


/-! # A record format that retains cross-class message order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
variable {X : Type} {k H : ℕ} (S : Spec X k H)

/-- The ordinal uses private bits. Neither endpoint needs to know
where in the other processor's message list it occurs. -/
abbrev OrderBits (j : Level k) := Slot S.messages (2 ^ j.val) k × (Strings.Position S.messages).pins

abbrev withOrder : Spec X k H :=
  { S.withStrings with guesses := fun g j => S.guesses g j + Fintype.card (S.OrderBits j) }

def orderPins (g j : Level k) : Fin (S.guesses g j) ⊕ S.OrderBits j ≃ Fin (S.withOrder.guesses g j) :=
  ((Equiv.refl _).sumCongr (Fintype.equivFin _)).trans finSumFinEquiv

variable {n : S.Who → ℕ} (j : S.Who → Level k) (row : Strings.Rows S.key n)
    (p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val)) (hm : ∀ i, n i ≤ S.messages)
    (f : (i : S.Who) → Fin (S.guesses i.1 (j i)) → Bool)

def ordered : S.withOrder.History :=
  S.withOrder.literal j row p fun i =>
    Sum.elim (f i) (fun a : S.OrderBits (j i) =>
      (Strings.Position S.messages).code (Strings.order row p hm i a.1) a.2) ∘
      (S.orderPins i.1 (j i)).symm

variable (a : S.withOrder.History)

abbrev recordLevel (i : S.Who) := (a i.1 i.2).1

def ordinals : Strings.Order S.messages k (fun i => 2 ^ (S.recordLevel a i).val) :=
  fun i v => (Strings.Position S.messages).code.symm
    fun b => (a i.1 i.2).2 (.inl (S.orderPins i.1 (S.recordLevel a i) (.inr (v, b))))

def recover : S.Who → ℕ → Option (Bool × S.key.obj × List Bool) :=
  Strings.restore (S.withOrder.declared a) (S.ordinals a)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
