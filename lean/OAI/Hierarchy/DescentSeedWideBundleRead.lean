import OAI.Hierarchy.DescentWideSeedHeader
import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentSeedTokenNumbers

namespace OAI
/-! # Reading eight census digits together from an original packed ballot -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSIMDLookup Catalyst Computability.VPVNP.BurstRAM
open Computability.VPVNP.RAMMemory (initialMemory)
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p R s : ℕ} (X : Approximation F k p) (h bw : ℕ)
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "M" => pieces h s

def bundles (sel : Select X R s→Bool) (v : Fin H) (j : Fin R) : Cell (d*8) :=
  groupedRows (cells X sel) v j

theorem wide_from_header (wide : 16*d≤h) (sel : Select X R s→Bool) (p : Row H R M) :
    initialMemory (headerWords X R s h) (wideBase X h bw sel) (publicWords X+(row H R M p).val)=
      ((data (bundles X sel) p).val:Word bw) := by
  have pos:0<M:=(occupancy h (8*d) (by unfold digitsNeeded;positivity) (by omega)).1
  let mem:=initialMemory (headerWords X R s h) (wideBase X h bw sel)
  have words : ∀j : Row H (R*8) (multiplicity h s),
      mem (publicWords X+(row H (R*8) (multiplicity h s) j).val)=((data (cells X sel) j).val:Word bw):=
    wide_data_at X h bw sel
  rw [grouped_multiplicity wide] at words
  exact regroup_read pos (by decide : 0<8) (publicWords X) mem (cells X sel) words p

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
