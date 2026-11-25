import OAI.Hierarchy.ProbeStripMenu

namespace OAI
/-! # Per-copy incidence of the genuine positive demands of a strip menu -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open AdaptiveProbe LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}

/-- From among all occurrences of a requested object, consume exactly its
positive-price copies selected by this catalogue entry. -/
def useBits (m : Probe.FixedMenu F edge req box ε tree N) (i : m.index) (e : E) : ℕ :=
  (m.packet i).width * Fintype.card {a : Probe.PositiveDemand req i.val.val // req a.1 = e}

theorem useBits_unique (m : Probe.FixedMenu F edge req box ε tree N) (i : m.index)
    (injective : Function.Injective req) (a : A) :
    useBits m i (req a) = if 0 < i.val.val (req a) then (m.packet i).width else 0 := by
  by_cases hi : 0 < i.val.val (req a)
  · let : Unique {b : Probe.PositiveDemand req i.val.val // req b.val=req a} :=
      {default:=⟨⟨a,hi⟩,rfl⟩,uniq:=fun b => Subtype.ext (Subtype.ext (injective b.2))}
    simp [useBits,hi]
  · let : IsEmpty {b : Probe.PositiveDemand req i.val.val // req b.val=req a} :=
      ⟨fun b => hi (b.2 ▸ b.1.2)⟩
    simp [useBits,hi]

theorem useBits_unused (m : Probe.FixedMenu F edge req box ε tree N) (i : m.index)
    (e : E) (ordinary : ∀ a, req a ≠ e) : useBits m i e=0 := by
  let : IsEmpty {b : Probe.PositiveDemand req i.val.val // req b.val=e} :=
    ⟨fun b => ordinary b.val.val b.2⟩
  simp [useBits]

variable {q : ℕ}

/-- A selector field outside the actual alphabet is a zero-width padded lane. -/
def installedBits (m : Probe.FixedMenu F edge req box ε tree N) (i : m.index)
    (e : E) (a : Fin q) : ℕ :=
  if ok : a.val < (m.packet i).terms then (m.packet i).count ⟨a.val,ok⟩ e else 0

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
