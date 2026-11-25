import OAI.Hierarchy.DescentExteriorContent
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # The seventeen exterior vote banks above the original ballot -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentExterior DescentGL Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory
open scoped Classical
noncomputable section
variable {w e j r t : ℕ}
set_option quotPrecheck false
local notation "H" => span j r t e
local notation "Hidden_" => Hidden e j r t

def image (endLow origin : ℕ) (old : Memory w) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : Hidden_→ Bool) :=
  staged origin (fun _=>LinearEquiv.refl _ _) x z (initialMemory endLow old)

theorem low (endLow origin : ℕ) (old : Memory w) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : Hidden_→ Bool)
    {a : ℕ} (sep : endLow ≤ origin) (below : a < endLow) : image endLow origin old x z a=old a := by
  have small : a < origin:=below.trans_le sep
  simp [image,staged,store,initialMemory,below,Nat.not_le_of_gt small]

theorem bounded (endLow origin : ℕ) (old : Memory w) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden_→Bool) (sep : endLow ≤ origin) :
    initialMemory (origin+17*H) (image endLow origin old x z)=image endLow origin old x z := by
  funext a
  by_cases inside : a < origin+17*H
  · simp [initialMemory,inside]
  · have outside : ¬a < endLow:=by omega
    simp [initialMemory,inside,image,staged,store,outside]

theorem loaded (endLow origin : ℕ) (old : Memory w) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : Hidden_→ Bool) :
    Loaded origin (fun _=>LinearEquiv.refl _ _) x z (image endLow origin old x z) :=
  staged_loaded origin (fun _=>LinearEquiv.refl _ _) x z (initialMemory endLow old)


end
end Hierarchy.DescentExteriorShelf.Root

end OAI
