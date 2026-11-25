import OAI.Hierarchy.ProbeStripBroadcastTree
import OAI.Hierarchy.ProbeStripOccupancy
import OAI.Hierarchy.TaggedWireWalkOrientation

namespace OAI
/-! # The actual one-hop strip wires and two-hop catalyst replacements -/
noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open scoped Classical BigOperators

variable {K N : ℕ} (edge : Fin N→Chord K)

/-- A physically unordered row may be traversed in either direction. -/
theorem one_hop (i : Fin N) {a b : Fin K} (ne : a≠b)
    (read : edge i=orderedEnds a b ne) : Traverses (rowGraph edge) a [i] b := by
  by_cases inc:a<b
  · have h:(edge i).val=(a,b):=by rw [read];simp [orderedEnds,inc]
    have tai:(rowGraph edge).tail i=a:=congrArg Prod.fst h
    have head:(rowGraph edge).head i=b:=congrArg Prod.snd h
    rw [←tai,←head];exact .forward i (.nil _)
  · have h:(edge i).val=(b,a):=by rw [read];simp [orderedEnds,inc]
    have tai:(rowGraph edge).tail i=b:=congrArg Prod.fst h
    have head:(rowGraph edge).head i=a:=congrArg Prod.snd h
    rw [←tai,←head];exact .backward i (.nil _)

theorem reverse_path {a b : Fin K} {r : List (Fin N)} (walk : Traverses (rowGraph edge) a r b) :
    Traverses (rowGraph edge) b r.reverse a := reversed (rowGraph edge) walk

variable {C H E Ball : Type} {k : ℕ} (horizontal : H→DistinctPair C)
    (extra : E→DistinctPair (ColumnSite C k))
    (place : Ball×ColumnSite C k↪Fin K) (u : Ball)
local notation "R" => ColumnWires.Role C H E k

/-- One `primary` index for the real native resource of each role.
The consumed virtual stock rows are addresses in the same combined graph.
A catalyst's second occurrence uses the literal opposite-radius ID. -/
def forward (primary : R→Fin N) (mate : C→Fin k→Fin N) : R→List (Fin N)
  | .catalyst c j=>[primary (.catalyst c j),mate c j]
  | r=>[primary r]

def firstRole : R→R
  | .catalyst c j=>.radius c j false
  | r=>r

def links (primary : R→Fin N) (mate : C→Fin k→Fin N) (r : R) :=
  let er:=ColumnWires.ends horizontal extra r
  if place (u,er.left)<place (u,er.right) then forward primary mate r else (forward primary mate r).reverse

theorem forward_path (primary : R→Fin N) (mate : C→Fin k→Fin N)
    (first : ∀r,edge (primary r)=reportedRole place (ColumnWires.ends horizontal extra) u (firstRole r))
    (second : ∀c j,edge (mate c j)=reportedRole place (ColumnWires.ends horizontal extra) u (.radius c j true))
    (r : R) :
    Traverses (rowGraph edge) (place (u,(ColumnWires.ends horizontal extra r).left))
      (forward primary mate r) (place (u,(ColumnWires.ends horizontal extra r).right)) := by
  have one (r : R) :=
    one_hop edge (primary r) (fun eq=>(ColumnWires.ends horizontal extra (firstRole r)).apart
      (congrArg Prod.snd (place.injective eq))) (first r)
  cases r with
  | catalyst c j=>
    let : Nonempty (Fin K) := ⟨place (u,(c,none))⟩
    have left := reverse_path edge (one (.catalyst c j))
    have right:=one_hop edge (mate c j) (fun eq=>(ColumnWires.ends horizontal extra (.radius c j true)).apart
      (congrArg Prod.snd (place.injective eq))) (second c j)
    exact Traverses.append (G:=rowGraph edge) left right
  | radius c j b=>exact one (.radius c j b)
  | cross c axes b d=>exact one (.cross c axes b d)
  | horizontal f l=>exact one (.horizontal f l)
  | extra e=>exact one (.extra e)

theorem path (primary : R→Fin N) (mate : C→Fin k→Fin N)
    (first : ∀r,edge (primary r)=reportedRole place (ColumnWires.ends horizontal extra) u (firstRole r))
    (second : ∀c j,edge (mate c j)=reportedRole place (ColumnWires.ends horizontal extra) u (.radius c j true))
    (r : R) :
    Traverses (rowGraph edge) (reportedRole place (ColumnWires.ends horizontal extra) u r).val.1
      (links horizontal extra place u primary mate r)
      (reportedRole place (ColumnWires.ends horizontal extra) u r).val.2 := by
  have walk:=forward_path edge horizontal extra place u primary mate first second r
  by_cases inc:place (u,(ColumnWires.ends horizontal extra r).left)<place (u,(ColumnWires.ends horizontal extra r).right)
  · simpa only [reportedRole,orderedEnds,dite_eq_left inc,links,ite_eq_left inc] using walk
  · simpa only [reportedRole,orderedEnds,dite_eq_right inc,links,ite_eq_right inc] using reverse_path edge walk

/-- Count by literal original native row index, even in the presence of
parallel edges or identical site pairs. Each printed primary contributes
once; precisely the catalyst rows contribute a mate. -/
theorem counts (primary : R→Fin N) (mate : C→Fin k→Fin N) (r : R) (v : Fin N) :
    (links horizontal extra place u primary mate r).count v =
      (if primary r=v then 1 else 0)+
        (match r with | .catalyst c j=>if mate c j=v then 1 else 0 | _=>0) := by
  have count : (links horizontal extra place u primary mate r).count v=(forward primary mate r).count v := by
    dsimp only [links]
    split <;> simp only [List.count_reverse]
  rw [count]
  cases r <;> simp only [forward,List.count_cons,List.count_nil,beq_iff_eq,Nat.zero_add,Nat.add_zero]; omega

/-- Every selector-tree edge uses exactly the indicated single paid core
row and has no share in either virtual stock or catalyst-mate streams. -/
theorem tree_path {n : ℕ} (place : Ball×TreeSite n k↪Fin K) (tree : TreeLink n k→Fin N)
    (read : ∀j,edge (tree j)=reportedRole place (treeEnds n k) u j) (j : TreeLink n k) :
    Traverses (rowGraph edge) (reportedRole place (treeEnds n k) u j).val.1 [tree j]
      (reportedRole place (treeEnds n k) u j).val.2 := by
  have h:=read j
  have tai:(rowGraph edge).tail (tree j)=(reportedRole place (treeEnds n k) u j).val.1:=congrArg (fun c=>c.val.1) h
  have head:(rowGraph edge).head (tree j)=(reportedRole place (treeEnds n k) u j).val.2:=congrArg (fun c=>c.val.2) h
  rw [←tai,←head];exact .forward _ (.nil _)

section Length
variable {n : ℕ}

/-- Each native role supplies one original resource or two original radii.
The public ordering of the pair of sites may reverse their order. -/
theorem links_length (horizontal : H → DistinctPair C) (extra : E → DistinctPair (ColumnSite C k))
    (place : Ball × ColumnSite C k ↪ Fin K) (u : Ball)
    (primary : R → Fin N) (mate : C → Fin k → Fin N) (r : R) :
    (links horizontal extra place u primary mate r).length ≤ 2 := by
  have short : (forward primary mate r).length ≤ 2 := by cases r <;> simp [forward]
  dsimp only [links]
  split
  · exact short
  · simpa only [List.length_reverse] using short

/-- The literal route field generated for an ordinary or selector-tree role. -/
theorem paths_length (horizontal : H → DistinctPair C) (extra : E → DistinctPair (ColumnSite C k))
    (place : Ball × ColumnSite C k ↪ Fin K) (u : Ball) (primary : R → Fin N)
    (mate : C → Fin k → Fin N) (tree : TreeLink n k → Fin N) (r : R ⊕ TreeLink n k) :
    (Sum.elim (links horizontal extra place u primary mate) (fun t => [tree t]) r).length ≤ 2 := by
  cases r with
  | inl i => exact links_length horizontal extra place u primary mate i
  | inr t => exact Nat.le_succ 1

end Length

end Hierarchy.WireTelescope.StripPaths

end
end OAI
