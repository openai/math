import OAI.Computability.BorderVNP.PackedInheritedFlatOrder

/-! # Retaining the final site programs at flat copy-and-port labels -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Adaptive

variable {k D M np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {R : Type*} (b : ℕ)
    [Fintype (Port k P b)] (p : Pack D (Port k P b) (width bits k b) R) (rows : p.layout.Edge ↪ Fin M)
    (portID : Port k P b ↪ Fin np) (v : p.layout.Site)

private abbrev L := (flattenPack b p).layout

private theorem flatWireOrd (c : Incident p.layout v) (j : Fin (p.layout.width c.val)) :
    sourceOrder (L b p) rows (Flat.portRows b portID) v (.inl ⟨c,j⟩) =
      Fin.cast (Flat.incoming_eq b p v).symm (sourceOrder p.layout rows portID v (.inl ⟨c,j⟩)) := by
  apply Fin.ext
  exact (wireOrdinal (L b p) _ _ _ c j).trans
    ((congrArg (·+j.val) (Flat.wireStart_eq b p rows portID v c)).trans (wireOrdinal p.layout _ _ _ c j).symm)

private theorem flatPortOrd (u : Attached p.layout v) (j : Fin (width bits k b u.val)) :
    sourceOrder (L b p) rows (Flat.portRows b portID) v (.inr ⟨Flat.attached b p v u,Fin.cast (width_portEquiv bits k b u.val) j⟩) =
      Fin.cast (Flat.incoming_eq b p v).symm (sourceOrder p.layout rows portID v (.inr ⟨u,j⟩)) := by
  apply Fin.ext
  exact (portOrdinal (L b p) _ _ _ (Flat.attached b p v u) _).trans
    ((congrArg (·+j.val) (Flat.portStart_eq b p rows portID v u)).trans (portOrdinal p.layout _ _ _ u j).symm)

/-- The final port relabeling reads the full nested input vector, including every exterior lane. -/
theorem flat_inputWords (z : ∀ c : Incident p.layout v, Fin (p.layout.width c.val) → Bool)
    (x : ∀ u : Attached (L b p) v, Fin (bits u.val.2) → Bool) (j : Fin (incoming p.layout v)) :
    inputWords (L b p) rows (Flat.portRows b portID) v z x (Fin.cast (Flat.incoming_eq b p v).symm j) =
      inputWords p.layout rows portID v z (fun u t => x (Flat.attached b p v u) (Fin.cast (width_portEquiv bits k b u.val) t)) j := by
  obtain ⟨t,rfl⟩ := (sourceOrder p.layout rows portID v).surjective j
  rcases t with ⟨c,j⟩ | ⟨u,j⟩
  · rw [←flatWireOrd]
    exact (inputWords_wire (L b p) _ _ _ z x c j).trans (inputWords_wire p.layout rows portID v z _ c j).symm
  · rw [←flatPortOrd]
    exact (inputWords_port (L b p) _ _ _ z x _ _).trans (inputWords_port p.layout rows portID v z
      (fun u t => x (Flat.attached b p v u) (Fin.cast (width_portEquiv bits k b u.val) t)) u j).symm

/-- The last epoch's program realizes its table on the actual flat copy ports. -/
theorem Site.Models.flattenPack [AddCommMonoid R] (s : Site) (hsize : s.incoming = Inherited.incoming p.layout v)
    (weight : List (Bool × Option ℕ) → R) (models : s.Models p.layout rows portID v hsize weight p.table) :
    let flat := Adaptive.flattenPack b p
    s.Models flat.layout rows (Flat.portRows b portID) v
      (hsize.trans (Flat.incoming_eq b p v).symm) weight flat.table := by
  dsimp only
  intro z x
  have hbits (j : Fin s.incoming) := flat_inputWords b p rows portID v z x (Fin.cast hsize j)
  exact (congrArg (s.value weight) (funext hbits)).trans (models _ _)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
