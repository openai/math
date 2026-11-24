import OAI.Computability.VPVNP.PrimedCounterCursor

/-!
# Chronological branch lists of the pair counter

The input and node calls have independent tapes. Clearing the marks, initializing
a root, and comparing histogram entries consume no branch bits. Reassembling
the two varying arrays and these empty tapes fixes every absolute cursor slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Chronology

variable {A S m K T : ℕ}

/-- A choice-bit list at each absolute position of the input, site and comparison schedule. -/
abbrev Tape (A S m K T : ℕ) := Fin (Cursor.calls A S m K T) → List Bool

/-- Read the private bit list at an input-assembly slot of the complete tape. -/
def inputPart (raw : Tape A S m K T) (i : Fin A) : List Bool :=
  raw (Cursor.index A S m K T (.inl i))

/-- Read the bit list for a given site's node visit after its mark-clearing and
root-initialization calls. -/
def nodePart (raw : Tape A S m K T) (u : Fin S) (j : Fin K) : List Bool :=
  raw (Cursor.index A S m K T (.inr (.inl (u, .inr (.inr j)))))

/-- The three administrative subroutines are deterministic at every call. -/
def AdminEmpty (raw : Tape A S m K T) : Prop :=
  (∀ (u : Fin S) (j : Fin m), raw (Cursor.index A S m K T (.inr (.inl (u, .inl j)))) = []) ∧
  (∀ (u : Fin S) (j : Fin 1), raw (Cursor.index A S m K T (.inr (.inl (u, .inr (.inl j))))) = []) ∧
  (∀ j : Fin T, raw (Cursor.index A S m K T (.inr (.inr j))) = [])

private def slotValue (inp : Fin A → List Bool) (nodes : Fin S → Fin K → List Bool) :
    Cursor.Item A S m K T → List Bool
  | .inl i => inp i
  | .inr (.inl (u, .inr (.inr j))) => nodes u j
  | .inr _ => []

private def pack (inp : Fin A → List Bool) (nodes : Fin S → Fin K → List Bool) :
    Tape A S m K T := slotValue inp nodes ∘ (Cursor.index A S m K T).symm

private theorem pack_admin (inp : Fin A → List Bool) (nodes : Fin S → Fin K → List Bool) :
    AdminEmpty (pack (m := m) (T := T) inp nodes) := by
  simp [AdminEmpty, pack, slotValue]

private theorem input_pack (inp : Fin A → List Bool) (nodes : Fin S → Fin K → List Bool) :
    inputPart (pack (m := m) (T := T) inp nodes) = inp := by
  funext i
  simp [inputPart, pack, slotValue]

private theorem node_pack (inp : Fin A → List Bool) (nodes : Fin S → Fin K → List Bool) :
    nodePart (pack (m := m) (T := T) inp nodes) = nodes := by
  funext u j
  simp [nodePart, pack, slotValue]

private theorem pack_parts (raw : Tape A S m K T) (h : AdminEmpty raw) :
    pack (inputPart raw) (nodePart raw) = raw := by
  funext t
  obtain ⟨i,rfl⟩ := (Cursor.index A S m K T).surjective t
  rcases i with i | (⟨u, j | (j | j)⟩ | j)
  · simp [pack, slotValue, inputPart]
  · simpa [pack, slotValue] using (h.1 u j).symm
  · simpa [pack, slotValue] using (h.2.1 u j).symm
  · simp [pack, slotValue, nodePart]
  · simpa [pack, slotValue] using (h.2.2 j).symm

/-- Every admitted input assignment specifies its entire array of input calls.
An injective input encoding lets us count the independent choices even when
they yield the same row data. -/
noncomputable def acceptedSlotsEquiv {α : Type*} (encode : α → Fin A → List Bool)
    (hinj : Function.Injective encode) (p : α → (Fin S → Fin K → List Bool) → Prop) :
    {raw : Tape A S m K T // ∃ a, inputPart raw = encode a ∧ AdminEmpty raw ∧ p a (nodePart raw)} ≃
      (Σ a : α, {nodes : Fin S → Fin K → List Bool // p a nodes}) := by
  let f (z : Σ a : α, {nodes : Fin S → Fin K → List Bool // p a nodes}) :
      {raw : Tape A S m K T // ∃ a, inputPart raw = encode a ∧ AdminEmpty raw ∧ p a (nodePart raw)} :=
    ⟨pack (encode z.1) z.2.val, z.1, input_pack .., pack_admin .., by rw [node_pack]; exact z.2.property⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · rintro ⟨a,bs⟩ ⟨a',bs'⟩ he
    have hp := congrArg Subtype.val he
    change pack (m := m) (T := T) (encode a) bs.val = pack (encode a') bs'.val at hp
    have h₁ := congrArg inputPart hp
    rw [input_pack, input_pack] at h₁
    obtain rfl := hinj h₁
    have h₂ := congrArg nodePart hp
    rw [node_pack, node_pack] at h₂
    exact congrArg (Sigma.mk a) (Subtype.ext h₂)
  · rintro ⟨raw,a,hi,ha,hn⟩
    refine ⟨⟨a,nodePart raw,hn⟩, Subtype.ext ?_⟩
    change pack (encode a) (nodePart raw) = raw
    rw [← hi, pack_parts raw ha]

end PrimedCounter.Chronology

end VPVNP
end Computability
end OAI
