import OAI.Computability.BorderVNP.DiagonalExternalFineView
import OAI.Computability.BorderVNP.DiagonalExternalSewPhysical
import OAI.Computability.BorderVNP.PackedBankInheritedValue
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # The actual input lanes of a retained site after exterior sewing

A host keeps its old internal cables. A formerly supplied scalar bit is
read either at its grouped free slot or at the physical interval cable
for the corresponding exterior pair. An unoccupied old slot reads zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew
open scoped Classical
open private localSlot from OAI.Computability.BorderVNP.DiagonalExternalSew
open private fill from OAI.Computability.BorderVNP.DiagonalExternalFineView

variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Free] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner

/-- A previously visible bit has become a grouped free lane or one endpoint of
a true external cable, possibly a loop at the same retained host. -/
def bundleLane (v : N.Site) :
    (t : Free ⊕ (Bool × (Σ c, Fin (cw c)))) → (FineView.layout N lane).attach (B.ports t) = v → InputLane out v
  | .inl f,h => .inr ⟨⟨(freeLane f).1,(aligned f).trans h⟩,(freeLane f).2⟩
  | .inr (false,⟨c,j⟩),h => .inl ⟨⟨.inr c,Or.inl ((B.atEnd c false j).symm.trans h)⟩,j⟩
  | .inr (true,⟨c,j⟩),h => .inl ⟨⟨.inr c,Or.inr ((B.atEnd c true j).symm.trans h)⟩,j⟩

local notation "slot" => bundleLane N lane B gw freeLane owner aligned

/-- Pull back each original incidence bit through the actual fine view,
exterior cable pairing, and grouping of the free literal and pin slots. -/
noncomputable def sewnLane (v : N.Site) : InputLane N v → Option (InputLane out v)
  | .inl ⟨e,j⟩ => some (.inl ⟨⟨.inl e.val,e.property⟩,j⟩)
  | .inr ⟨a,j⟩ =>
    if h : ∃ p, lane p = ⟨a.val,j⟩ then
      let p := h.choose
      have hp : (FineView.layout N lane).attach p = v :=
        (congrArg (fun k : Σ a, Fin (width a) => N.attach k.1) h.choose_spec).trans a.property
      some (slot v (B.ports.symm p) ((congrArg (FineView.layout N lane).attach (B.ports.apply_symm_apply p)).trans hp))
    else none

variable {ae ap be bp : ℕ} (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp)

/-- Old and new physical site ordinals use their own current edge and port
directories. A missing fine lane has no new source ordinal. -/
noncomputable def sewnRead (v : N.Site) (i : Fin (incoming N v)) : Option (Fin (incoming out v)) :=
  Option.map (sourceOrder out edge port v)
    (sewnLane N lane B gw freeLane owner aligned v ((sourceOrder N oldEdge oldPort v).symm i))

local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port

omit [Fintype Free] in
/-- All original incident fields are read at their true new source ordinals
when the exterior pairing and the free port groups supply the table input. -/
theorem sewnRead_table {K : Type*} (T : N.Tables K) (v : N.Site)
    (z : ∀ e : Incident out v, Fin ((out).width e.val) → Bool) (x : ∀ p : Attached out v, Fin (gw p.val) → Bool) :
    let oldZ := fun e : Incident N v => z ⟨.inl e.val,e.property⟩
    let free := fun f : Attached B.layout v => fun _ : Fin 1 => x ⟨(freeLane f.val).1,(aligned f.val).trans f.property⟩ (freeLane f.val).2
    let fine := fun p : Attached (FineView.layout N lane) v => localSlot B v z free (B.ports.symm p.val)
      ((congrArg (FineView.layout N lane).attach (B.ports.apply_symm_apply _)).trans p.property)
    let oldX := fun a : Attached N v => fun j : Fin (width a.val) => fill lane ⟨a.val,j⟩ fun p hp =>
      fine ⟨p,(congrArg (fun k : Σ a, Fin (width a) => N.attach k.1) hp).trans a.property⟩ 0
    (∀ k, (read₀ v k).elim false (inputWords out edge port v z x) = inputWords N oldEdge oldPort v oldZ oldX k) ∧
      (B.layout.externalTables gw freeLane owner aligned (B.tables (FineView.tables N lane T)) v z x = T v oldZ oldX) := by
  intro oldZ free fine oldX
  refine ⟨?_,rfl⟩
  intro k
  obtain ⟨l,rfl⟩ := (sourceOrder N oldEdge oldPort v).surjective k
  rcases l with ⟨e,j⟩ | ⟨a,j⟩
  · simp only [sewnRead,Equiv.symm_apply_apply,sewnLane,Option.map_some,Option.elim_some]
    exact (inputWords_wire out edge port v z x _ _).trans (inputWords_wire N oldEdge oldPort v oldZ oldX e j).symm
  · rw [inputWords_port N oldEdge oldPort v oldZ oldX a j]
    simp only [sewnRead,Equiv.symm_apply_apply,sewnLane,oldX,fill]
    split
    · rename_i h
      let p := h.choose
      let hp : (FineView.layout N lane).attach p = v :=
        (congrArg (fun k : Σ a, Fin (width a) => N.attach k.1) h.choose_spec).trans a.property
      have pull (t : Free ⊕ (Bool × (Σ c, Fin (cw c)))) (ht : (FineView.layout N lane).attach (B.ports t) = v) :
          inputWords out edge port v z x (sourceOrder out edge port v (slot v t ht)) = localSlot B v z free t ht 0 := by
        rcases t with f | ⟨side,c,j'⟩
        · exact inputWords_port out edge port v z x _ _
        · cases side <;> exact inputWords_wire out edge port v z x _ _
      exact pull (B.ports.symm p) ((congrArg (FineView.layout N lane).attach (B.ports.apply_symm_apply _)).trans hp)
    · rfl

end Packing.SewnField

end BorderVNP
end Computability
end OAI
