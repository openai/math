import OAI.Computability.BorderVNP.CubePhysicalEnds

/-! # Placing each packet's vertices at its actual product-alphabet labels

Reversing a packet's public orientation flips the first cube coordinate.
The source and destination of every antipodal pair then agree with the
two labels attached to its original padded slot. A cube-edge bit changes
the chosen symbol exactly in its own coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

variable {n d blocks width : ℕ}

/-- The symbol choices of an abstract packet vertex in its concrete cube. -/
def cornerBits (p : Packet n d blocks) (v : Vertex (n+1)) : Fin (n+1) → Bool :=
  fun j => if j = 0 then xor (finTwoEquiv (v j)) p.1.2 else finTwoEquiv (v j)

/-- The product-alphabet label of an actual packet vertex. -/
def vertexLabel (p : Packet n d blocks) (v : Vertex (n+1)) : Label (n+1) d :=
  fun j => if cornerBits p v j then (p.1.1 j).val.2 else (p.1.1 j).val.1

private theorem bit_flip (x : ZMod 2) : finTwoEquiv ((x + (1 : ZMod 2)) : ZMod 2) = !(finTwoEquiv x) := by
  decide +revert

private theorem corner_start (p : Packet n d blocks) (v : Vertex n) :
    cornerBits p (start v) = Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun j => finTwoEquiv (v j)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · change xor false p.1.2 = p.1.2
    cases p.1.2 <;> rfl
  · simp [cornerBits, start]

private theorem corner_stop (p : Packet n d blocks) (v : Vertex n) :
    cornerBits p (stop v) = fun j => !(Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun k => finTwoEquiv (v k)) j) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · change xor true p.1.2 = !p.1.2
    cases p.1.2 <;> rfl
  · simp [cornerBits, stop, start, bit_flip]

/-- Both labels of an original full-pair slot are the two actual antipodal
vertices used by its selected local tables. -/
theorem inverseSlot_labels (p : Packet n d blocks) (v : Vertex n) (j : Fin width) :
    ((splitSlot n d blocks width).symm (.inl (p, v, j))).1 =
      (vertexLabel p (start v), vertexLabel p (stop v)) := by
  apply Prod.ext <;> funext i
  · unfold vertexLabel
    rw [corner_start]
    rfl
  · unfold vertexLabel
    rw [corner_stop]
    change (if Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun k => finTwoEquiv (v k)) i then _ else _) =
      (if !(Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun k => finTwoEquiv (v k)) i) then _ else _)
    cases Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun k => finTwoEquiv (v k)) i <;> rfl

/-- An actual internal cube edge changes its label only in its own coordinate.
That bit therefore crosses exactly one of the candidate grouping cuts. -/
theorem vertexLabel_head_eq_iff (p : Packet n d blocks) (e : Edge (n+1)) (j : Fin (n+1)) :
    vertexLabel p (head e) j = vertexLabel p e.1 j ↔ j ≠ e.2 := by
  have distinct := (p.1.1 j).property.ne
  by_cases h : j = e.2
  · subst j
    have hflip : cornerBits p (head e) e.2 = !(cornerBits p e.1 e.2) := by
      have he : head e e.2 = e.1 e.2 + (1 : ZMod 2) := by simp [head, step]
      simp only [cornerBits, he, bit_flip]
      split <;> first | rfl | (cases finTwoEquiv (e.1 e.2) <;> cases p.1.2 <;> rfl)
    simp only [vertexLabel, hflip, ne_self_iff_false, iff_false]
    cases cornerBits p e.1 e.2 <;> simp [distinct, Ne.symm distinct]
  · have he : head e j = e.1 j := by simp [head, step, Pi.single_eq_of_ne h]
    have bits : cornerBits p (head e) j = cornerBits p e.1 j := by
      simp only [cornerBits, he]
    simp [vertexLabel, bits, h]

end Cube.Physical

end BorderVNP
end Computability
end OAI
