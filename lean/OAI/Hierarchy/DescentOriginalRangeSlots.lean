import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # The three interval digits at each original argument ordinal -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory
noncomputable section
variable {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}

/-- One descriptor per actual operand, in the primitive's original row and chunk order. -/
def occurrences (s : Shape p r) (u : r.Node) : List SliceCode :=
  (s.rows u).flatMap (List.flatMap (fun q=>List.replicate q.count q.code))

def value (c : SliceCode) (j : Fin 3) : ℕ:=if j.val=0 then c.start else if j.val=1 then c.stride else c.count
def atSlot (s : Shape p r) (u : r.Node) (slot : ℕ) (f : Fin 3) : ℕ :=
  ((occurrences s u)[slot]?).elim 0 (fun q=>value q f)

theorem length (s : Shape p r) (u : r.Node) (hp : 0<p) :
    (occurrences s u).length=(s.recipe hp).arity u:=by
  simp [occurrences,Shape.recipe,Shape.keys,Slice.names,List.length_flatMap]


end
end Hierarchy.DescentRetainedRangeDigits

end OAI
