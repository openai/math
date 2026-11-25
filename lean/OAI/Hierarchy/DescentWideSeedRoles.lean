import OAI.Hierarchy.DescentWideSeedPublication
import OAI.Hierarchy.DescentSeedWideBundleRead
import OAI.Hierarchy.DescentWideSeedRoleCode

import OAI.Hierarchy.DescentWideSeedHeader
import OAI.Hierarchy.DescentSeedCensusRAM
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Mounted census role tables for short seed lanes on a wide machine -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSIMDLookup DescentPackedColony.Phase.Arena Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p R s : ℕ} (X : Approximation F k p) (h bw : ℕ)
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "M" => pieces h s
local notation "n" => H*chunks R M
local notation "T" => fun start=>tape start H R M s (publicWords X)

theorem wide_role {cw : ℕ} (fit : s<2^cw) (active : 0<M) (hw : h≤bw)
    (c : (initialGroup X R s).Choice) (out : ℕ) (mem : Memory bw)
    (issued : ∀p : Row H R M,mem (out+(row H R M p).val)=
      ((data (fun v j=>entry s (sitePlan X v) (bundles X (selectBit X cw c) v j)) p).val:Word bw))
    (v : Old X) (j : Fin R) :
    let loc:=position ((Fintype.equivFin _) v) j active
    digit (roleBits s) (lane j active).val (mem (out+(row H R M loc).val)).val=
      ((DescentEpochTagKeys.census s).store (DescentPrimitivePalette.seedRole X R c j (.inl v))).val :=
  Spaced.read_primitive X fit active c out mem ((result_fit h s).trans hw) issued v j

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
