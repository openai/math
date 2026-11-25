import OAI.Computability.BorderVNP.PackedInheritedWorkStep
import OAI.Computability.BorderVNP.PackedHistoryRetainedFrame

/-! # Work-width side output of a shared geometric node

The old width words, selected histogram, and saved endpoint pointers are
literal aliases in the joint selected-node frame. The geometric pass runs
once, and its guard and directory remain available for the following node.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening.StaticRows Shortening.PublicSegments
open PackedHistoryCircuit VPVNP.VerifierNetwork
open scoped Classical

variable {D m k V E n np w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A B Old : Type} [Fintype A] [Fintype B] [Fintype Old]

/-- Previous geometry, both previous site widths and the current guessed profile. -/
abbrev WidthInput (Old A : Type) (k V count w : ℕ) :=
  (Fin k × (Old ⊕ (Fin V × Bool × Fin w))) ⊕ (A × Fin count × Fin w)

/-- Geometric result of the normalized saved node in its padded rectangles. -/
abbrev SavedPins (B : Type) (V E w : ℕ) := Fin E ⊕ Raw B V E w w

local notation3 "outV" => siteCapacity e (k*V) n
local notation3 "Pre" => WidthInput Old A k V e.count w
local notation3 "Geo" => SavedPins B outV E w

variable (seed : A ↪ Fin n) (host width : Fin np → ℕ) (fit : siteCapacity e (k*V) n ≤ 2^w)

/-- Read the extents from the child inputs, the actual guess from the current
node, and the endpoint fields from its newly emitted geometric directory. -/
def jointFields : NodeFields (A := A) (k := k) (V := V) (E := E) (n := n) (np := np) (w := w) e B
    (WidthInput Old A k V e.count w ⊕ (SavedPins B (siteCapacity e (k*V) n) E w ⊕ Unit)) where
  child z := .inl (.inl (z.1,.inr (z.2.1,true,z.2.2)))
  guess z := .inl (.inr z)
  saved z := .inr (.inl (.inr (.inr z)))
  host := host
  width := width
  siteFit := fit

variable (geom : Frame ((Fin k × Old) ⊕ (A × Fin e.count × Fin w)) (SavedPins B (siteCapacity e (k*V) n) E w ⊕ Unit))

private noncomputable abbrev shape : Frame Pre (Geo ⊕ Unit) := geom.subst (Frame.initial (Sum.map (fun z => (z.1,Sum.inl z.2)) id))

/-- The selected geometric circuit and its true width emitter, with one
common evaluation of the predecessor and newly saved endpoint pins. -/
noncomputable def jointNode : Frame (WidthInput Old A k V e.count w)
    ((SavedPins B (siteCapacity e (k*V) n) E w ⊕ (Fin (siteCapacity e (k*V) n) × Bool × Fin w)) ⊕ Unit) :=
  Retained.joint (Frame.initial id) (shape e geom) (node e seed (jointFields e host width fit))

theorem jointNode_size : (jointNode e seed host width fit geom).size =
    geom.size + (node e seed (jointFields (Old := Old) (B := B) (E := E) e host width fit)).size := by
  simp [jointNode,Retained.joint_size,shape]

/-- The stored widths are precisely the gate result on the assigned old rows,
current histogram, and selected saved geometry of this same node. -/
theorem jointNode_words (x : Pre → Bool) (i : Fin (siteCapacity e (k*V) n)) (b : Bool) (j : Fin w) :
    (jointNode e seed host width fit geom).eval x (.inl (.inr (i,b,j))) =
      (node e seed (jointFields e host width fit)).eval
        (Sum.elim x ((shape e geom).eval x)) (i,b,j) := by
  have h := Retained.joint_words (Frame.initial id) (shape e geom) (node e seed (jointFields e host width fit)) x (i,b,j)
  have hx : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
  simpa only [jointNode,hx] using h

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
