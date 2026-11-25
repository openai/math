import OAI.Computability.BorderVNP.PrivatePlacementBank
import OAI.Computability.BorderVNP.PrivatePlacementProof
import OAI.Computability.BorderVNP.PackedDirectoryEval

/-! # The populated native frame supplies the separated cell-bank placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.PrivateBank

open Function RoutingISA
open scoped Classical

/-- The first placement table is the actual output of the per-cell native prefix
pass. Its second word follows the entire supplied-input region. The live placement
table stays verbatim in the protected suffix and addresses the supplied words. -/
def ofNativeImage {d : Layout} {w cells M : ℕ} {A : Type*} [Fintype A]
    (supplyCell : A → Fin cells) (id : A ↪ Fin M) (width : A → ℕ)
    (oldCell : Fin d.entries → Fin cells) (live : (Fin d.teams × Fin d.sites) ↪ A)
    (liveWidth : ∀ k, width (live k) = d.block)
    (l : PrivatePlacement.Layout) (before after : ℕ → ℕ)
    (image : l.Image before l.entries after) (fit : l.Fits w before)
    (entries : l.entries = d.entries) (desc : l.desc = d.description)
    (owners : ∀ j : Fin d.entries, l.owner before j.val = (oldCell j).val)
    (counts : ∀ c : Fin cells, before (l.supplied+c.val)+l.gap = DataSlabs.size supplyCell width c)
    (liveBase : ℕ) (separateRaw : l.raw+2*l.entries ≤ liveBase)
    (separateCounters : l.scratch+l.cells ≤ liveBase)
    (liveRows : ∀ k : Fin d.teams × Fin d.sites, ISA.placement before liveBase (k.1.val*d.sites+k.2.val) =
      ((supplyCell (live k)).val, DataSlabs.base supplyCell (id.trans Fin.valEmbedding) width (live k))) :
    BankPlacement d (ISA.placement after l.raw) (ISA.placement after liveBase) (A ⊕ Fin d.entries)
      (Sum.elim supplyCell oldCell) (numbered id) (Sum.elim width fun _ => d.description) := by
  apply placement supplyCell id width _ _ oldCell (l.owner before) owners live liveWidth
  · intro j
    have hj : j.val < l.entries := by simpa only [entries] using j.isLt
    have first := image.owner_eq fit hj
    have second := image.slots j.val hj
    simp only [owners j,counts,desc] at second
    exact Prod.ext (by simpa only [ISA.placement,Nat.mul_comm j.val 2] using first.trans (owners j))
      (by simpa only [ISA.placement,Nat.mul_comm j.val 2] using second)
  · intro k
    have unchanged (x : ℕ) (hx : liveBase ≤ x) : after x = before x :=
      image.outside x (fun j hj => by omega) (Or.inr (separateCounters.trans hx))
    rw [← liveRows k]
    apply Prod.ext
    · exact unchanged _ (Nat.le_add_right ..)
    · exact unchanged _ (by omega)

end Packing.Directory.PrivateBank

end BorderVNP
end Computability
end OAI
