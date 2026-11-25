import OAI.Computability.BorderVNP.PackedNativeDemandDestination
import OAI.Computability.BorderVNP.PackedBundleGeometryHeaders

/-! # Header addresses at an original's attained native private placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Diagonal.ExternalSew CellAddresses CellAddressPhysical CellAddressCircuit BottomReports RoutingISA
open VPVNP.VerifierNetwork
open scoped Classical

variable {D C m n s d k w J : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (sid : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : P ↪ Fin n) (dir : Directory.Layout)
    (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    {σ : Type} [Fintype σ] (F : Fields s m n C d k w σ) (x : σ → Bool)
    (net : Represents N cell aux sid edge port F x) (code : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)

include net code fit in
/-- The public geometry header uses the very receiving-bank and local work
offset of the original that occurs in the native demand directory. -/
theorem placed_bundle_header (head origin recv bank stride logicalWord : ℕ)
    (before placed after : ℕ → ℕ) (shape : Fin dir.entries → BundleSort.Shape)
    (width : ∀ p, bits (live p) = dir.block)
    (image : Image F (sid ∘ old) (port ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin m C dir.entries dir.description gap).Image before dir.entries placed)
    (room : (privateLayout head origin m C dir.entries dir.description gap).Fits logicalWord before)
    (keep : ∀ i : Fin dir.entries, let raw := (bases origin m C dir.entries).privatePairs
      after (raw+2*i.val)=placed (raw+2*i.val) ∧ after (raw+2*i.val+1)=placed (raw+2*i.val+1))
    (banks : ∀ c : Fin C, after (recv+2*c.val+1)=bank+c.val*stride) (j : Fin dir.entries) :
    let l := privateLayout head origin m C dir.entries dir.description gap
    let sh := shape j
    let slot := bank+(cell (old j)).val*stride+(destination N cell edge port dir old live gap (.inl j)).2
    let base := siteBase N cell (cell (old j)) sid aux ⟨old j,rfl⟩
    geometryHeader (Retains.id N) sid F (x:=x) l after recv old j sh.copies sh.fine sh.incoming sh.cap =
      sh.header slot base := by
  intro l sh slot base
  have placement := placed_destination N cell edge port dir old live gap aux sid F x head origin before placed
    net code fit width image run room (.inl j)
  let raw := (bases origin m C dir.entries).privatePairs
  have coords : (placed (raw+j.val*2),placed (raw+j.val*2+1))=
      ((cell (old j)).val,(destination N cell edge port dir old live gap (.inl j)).2) := placement
  rw [Nat.mul_comm j.val 2] at coords
  have hi : after (raw+2*j.val)=(cell (old j)).val := (keep j).1.trans (congrArg Prod.fst coords)
  have lo : after (raw+2*j.val+1)=(destination N cell edge port dir old live gap (.inl j)).2 :=
    (keep j).2.trans (congrArg Prod.snd coords)
  have address : (geometryHeader (Retains.id N) sid F (x:=x) l after recv old j sh.copies sh.fine sh.incoming sh.cap).siteSlot=slot := by
    change after (recv+2*after (raw+2*j.val)+1)+after (raw+2*j.val+1)=_
    rw [hi,lo,banks]
  have offset := geometry_base (Retains.id N) cell aux sid edge port F net fit l after recv old j
    sh.copies sh.fine sh.incoming sh.cap
  exact congrArg₂ sh.header address offset

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
