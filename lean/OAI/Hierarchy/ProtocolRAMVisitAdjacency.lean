import OAI.Hierarchy.ProtocolRAMTurnOrder
import OAI.Hierarchy.TaggedWireVisitOrder

namespace OAI
/-! # The forward endpoint recurrence on the actual chronological turn ordinal -/

namespace Hierarchy.ProtocolRAMVisitAdjacency

open WireTelescope.VisitOrder ProtocolRAMTurnOrder
variable {k : ℕ} {E : Type*}

def vertex (len : Fin k → ℕ) (visit : Fin k → ℕ → ℕ) (i : Fin (turns len)) : ℕ :=
  visit (raw len i).1 (raw len i).2.val

/-- This is the endpoint-sum witness consumed by the actual pointer-based native
walk. The ring formula is invariant under reversing either occurrence orientation. -/
theorem adjacent (len origin : Fin k → ℕ) (visit : Fin k → ℕ → ℕ)
    (walk : Fin k → List E) (edges : E → ℕ×ℕ) (paid : ℕ → E)
    (shape : ∀a,(walk a).length=len a)
    (read : ∀ (a : Fin k) (j : ℕ) (h : j < (walk a).length),paid (origin a+j)=(walk a)[j])
    (path : ∀a,Steps edges (visit a) 0 (walk a)) (i : Fin (turns len)) (h : 0 < (raw len i).2.val) :
    let item := (raw len i).1
    let pos := (raw len i).2.val
    let e := edges (paid (origin item+(pos-1)))
    e.1+e.2 = vertex len visit i+vertex len visit ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ := by
  intro item pos e
  have bound : pos ≤ len item := Nat.le_of_lt_succ (raw len i).2.isLt
  have plain : 0 < pos := h
  have old : pos-1 < (walk item).length := by rw [shape];omega
  have arc := path item (pos-1) old
  simp only [Nat.zero_add,show pos-1+1=pos by omega] at arc
  have prior : vertex len visit ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩=visit item (pos-1) := by
    unfold vertex
    rw [previous_eq len i h]
  rw [prior]
  change (edges (paid (origin item+(pos-1)))).1+(edges (paid (origin item+(pos-1)))).2=
    visit item pos+visit item (pos-1)
  rw [read item (pos-1) old]
  rcases arc with ⟨l,r⟩|⟨r,l⟩
  · rw [l,r,Nat.add_comm]
  · rw [l,r]

end Hierarchy.ProtocolRAMVisitAdjacency

end OAI
