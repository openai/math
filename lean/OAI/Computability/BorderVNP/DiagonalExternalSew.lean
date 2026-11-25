import OAI.Computability.BorderVNP.DiagonalTaggedStep

/-! # Closing paired external bits at the actual stored host sites

The two occurrences of an exterior bit share one position in a cable.
Consecutive bit positions may occupy a single cable when both attachment
sites agree throughout the interval. A cable may also be a loop. The old
vertex boxes remain in place and each occurrence of a free bit continues
to read the slot at its own vertex.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening CellEntries
open scoped Classical BigOperators

variable {D : ℕ} {P Free Cable : Type} [Fintype Cable]

/-- The public partition of stored input slots into free bits and the two
ordered ends of each interval of exterior wires. -/
structure Bundle (N : Network D P (fun _ => 1)) (Free Cable : Type) (width : Cable → ℕ) where
  /-- The physical port for each remaining input and each linked endpoint bit. -/
  ports : Free ⊕ (Bool × (Σ c, Fin (width c))) ≃ P
  /-- Actual stored host of the low-team or high-team end of a cable. -/
  endpoint : Cable → Bool → N.Site
  atEnd : ∀ c side j, N.attach (ports (.inr (side,⟨c,j⟩))) = endpoint c side

namespace Bundle

variable {width : Cable → ℕ} {N : Network D P (fun _ => 1)} (B : Bundle N Free Cable width)

/-- The exterior cable goes directly between its two stored attachments.
Coincident attachments retain the same cable assignment at both occurrences. -/
def layout : Network D Free (fun _ => 1) where
  Site := N.Site
  Edge := N.Edge ⊕ Cable
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim N.src (fun c => B.endpoint c false)
  dst := Sum.elim N.dst (fun c => B.endpoint c true)
  width := Sum.elim N.width width
  attach f := N.attach (B.ports (.inl f))
  position := N.position
  in_ball := N.in_ball

/-- Read a free input or the indexed bit of a shared exterior cable. -/
def slotValue (x : Ports (fun _ : Free => 1)) (y : Ports width) :
    Free ⊕ (Bool × (Σ c, Fin (width c))) → Fin 1 → Bool
  | .inl f => x f
  | .inr (_,⟨c,j⟩) => fun _ => y c j

/-- Assignment to the ports of the original compressed pack. -/
def joined (x : Ports (fun _ : Free => 1)) (y : Ports width) : Ports (fun _ : P => 1) :=
  fun p => slotValue x y (B.ports.symm p)

private def localSlot (v : N.Site)
    (z : ∀ e : {e : B.layout.Edge // B.layout.src e = v ∨ B.layout.dst e = v},
      Fin (B.layout.width e.val) → Bool)
    (x : {f : Free // B.layout.attach f = v} → Fin 1 → Bool) :
    (s : Free ⊕ (Bool × (Σ c, Fin (width c)))) → N.attach (B.ports s) = v → Fin 1 → Bool
  | .inl f, h => x ⟨f,h⟩
  | .inr (false,⟨c,j⟩), h => fun _ => z ⟨.inr c,Or.inl ((B.atEnd c false j).symm.trans h)⟩ j
  | .inr (true,⟨c,j⟩), h => fun _ => z ⟨.inr c,Or.inr ((B.atEnd c true j).symm.trans h)⟩ j

/-- Each unchanged local table reads its original incident cables and the
appropriate stored positions in its external interval cables. -/
def tables {R : Type*} (T : N.Tables R) : B.layout.Tables R := fun v z x =>
  T v (fun e => z ⟨.inl e.val,e.property⟩) (fun p =>
    B.localSlot v z x (B.ports.symm p.val) ((congrArg N.attach (B.ports.apply_symm_apply _)).trans p.property))

private theorem localSlot_shared (a : B.layout.Assignment) (x : Ports (fun _ : Free => 1))
    (v : N.Site) (s : Free ⊕ (Bool × (Σ c, Fin (width c)))) (h : N.attach (B.ports s) = v) :
    B.localSlot v (fun e => a e.val) (fun p => x p.val) s h =
      slotValue x (fun c => a (.inr c)) s := by
  rcases s with f | ⟨side,c,j⟩
  · rfl
  · cases side <;> rfl

/-- For a complete cable assignment the local table reads both exterior
occurrences from exactly the bit shared by their two stored sites. -/
theorem read {R : Type*} (T : N.Tables R) (a : B.layout.Assignment) (x : Ports (fun _ : Free => 1))
    (v : N.Site) : B.layout.read (B.tables T) a x v =
      N.read T (fun e => a (.inl e)) (B.joined x (fun c => a (.inr c))) v := by
  apply congrArg (T v (fun e => a (.inl e.val)))
  funext p
  exact B.localSlot_shared a x v (B.ports.symm p.val) _

/-- Sewing the compressed pack sums once over each external bit, for
every fixed setting of the literal and index slots. -/
theorem value {R : Type*} [CommSemiring R] (T : N.Tables R) (x : Ports (fun _ : Free => 1)) :
    B.layout.value (B.tables T) x = ∑ y : Ports width, N.value T (B.joined x y) := by
  let eqv : B.layout.Assignment ≃ Ports width × N.Assignment :=
    (Equiv.sumPiEquivProdPi (fun e : N.Edge ⊕ Cable => Fin (Sum.elim N.width width e) → Bool)).trans
      (Equiv.prodComm _ _)
  let term := fun y : Ports width × N.Assignment => ∏ v, N.read T y.2 (B.joined x y.1) v
  have hs : B.layout.value (B.tables T) x = ∑ y, term y := by
    unfold Network.value
    apply Fintype.sum_equiv eqv _ _
    intro a
    apply Finset.prod_congr rfl
    intro v _
    exact B.read T a x v
  exact hs.trans (Fintype.sum_prod_type term)

/-- The unary use bits continue to be owned by their original boxes. Each
owner's read uses the same free and paired cable positions as its tag. -/
def words {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}
    {tags : N.Tables (Entry Param Gadget)} (w : PowerWords Team Param Gadget b N tags) :
    PowerWords Team Param Gadget b B.layout (B.tables tags) where
  site := w.site
  selected := B.tables w.selected
  located v _ _ i h := w.located v _ _ i h
  exact v _ _ := w.exact v _ _

/-- The actual sewn layout with all conditioned factors and unary readers. -/
def tracked {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}
    (t : Tracked Team Param Gadget b N) : Tracked Team Param Gadget b B.layout :=
  ⟨B.tables t.tags,B.words t.words⟩

/-- Sewing preserves the full formal parameter-polynomial expansion under
every assignment to the gadget values. -/
theorem tracked_tensor {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param] [CommSemiring E]
    {b : ℕ} (t : Tracked Team Param Gadget b N) (values : Gadget → E) (x : Ports (fun _ : Free => 1)) :
    ((B.tracked t).valued values).tensor x =
      ∑ y : Ports width, (t.valued values).tensor (B.joined x y) :=
  B.value (t.valued values).table x

end Bundle
end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
