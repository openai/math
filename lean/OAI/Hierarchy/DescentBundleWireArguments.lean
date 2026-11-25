import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # Incident cable references at flattened bundle operands -/
namespace Hierarchy.DescentResetFreshWires
open DescentKernelHistory DescentBundleHistory Computability.BorderVNP.Crossing
noncomputable section
variable {p d : ℕ} {P T : Type} {bits : P→ℕ} {N : Network d P bits}

def IsWire {β : Type} (v : N.Site) (word : BlockRef p (boundaryWidth N v)⊕β) : Prop :=
  ∃(ref : BlockRef p (boundaryWidth N v)) (e : Incident N v),word=.inl ref ∧ ref.port=.inl e

def OnlyWires {v : N.Site} {r : BitRecipe T (Boundary N v) (boundaryWidth N v)}
    (s : Shape p r) (u : r.Node) : Prop :=
  ∀j g i,IsWire (N:=N) v ((s.chunk u j g).get i)

theorem flat_wire {v : N.Site} {r : BitRecipe T (Boundary N v) (boundaryWidth N v)}
    {s : Shape p r} {u : r.Node} (all : OnlyWires (N:=N) (v:=v) s u) (i : Fin (s.keys u).length) :
    IsWire (N:=N) v ((s.keys u)[i.val]) :=by
  have member:=List.getElem_mem i.isLt
  change (s.keys u)[i.val]∈(s.rows u).flatMap (List.flatMap Slice.names) at member
  obtain ⟨row,rowMem,within⟩:=List.mem_flatMap.mp member
  obtain ⟨chunk,chunkMem,occ⟩:=List.mem_flatMap.mp within
  obtain ⟨j,hrow⟩:=List.mem_ofFn.mp rowMem
  subst row
  obtain ⟨g,hg⟩:=List.mem_ofFn.mp chunkMem
  subst chunk
  obtain ⟨i',hi'⟩:=List.mem_ofFn.mp occ
  rw [←hi']
  exact all j g i'

end
end Hierarchy.DescentResetFreshWires

end OAI
