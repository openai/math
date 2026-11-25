import OAI.Hierarchy.ProtocolRAMCatalystChargedSlab
import OAI.Hierarchy.ProbeFixedNativeBoards

namespace OAI
/-! # Fixed physical start and end of the original signed archive -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard
open CoreRoute BoughtSockets CatalogueRows CatalystArchive
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "s" => v.nativeBoards P z width
local notation "d" => 2^v.W

def catalystPairStart :=
  (v.emptyReserve P z width).base+(v.emptyReserve P z width).size+2^(GlobalTests.bits z (Stages z d) k)

def catalystPairOwners := Slab.pairOwners (v.catalystPairStart P z width) (Fintype.card (Slots z d k))
def catalystPairParity := Slab.pairParity (v.catalystPairStart P z width) (Fintype.card (Slots z d k))
def catalystStaticStart := (v.catalystPairParity P z width).base+(v.catalystPairParity P z width).size

theorem reserve_before_catalystStaticStart :
    (v.emptyReserve P z width).base+(v.emptyReserve P z width).size≤v.catalystStaticStart P z width := by
  let start:=v.catalystPairStart P z width
  let occ:=v.catalystPairOwners P z width
  let parity:=v.catalystPairParity P z width
  calc
    _ ≤ start := Nat.le_add_right ..
    _ ≤ start+occ.size := Nat.le_add_right ..
    _ ≤ start+occ.size+parity.size := Nat.le_add_right ..

theorem catalyst_static_before :
    v.catalystStaticStart P z width≤(v.privateArena P z width).first :=
  Slab.staticStart_before
    (chargedSlab F (v.sized (v.seed P z width) width) v.cost (v.publicHeader P z width)
      (ProtocolRAMPurchaseSampler.bits v.keepLimit))
    v.mesh z d k (v.sized (v.seed P z width) width).sampler.degree v.depth P.catalogue.rows

theorem catalyst_pair_fits (w : ℕ) (room : (v.privateArena P z width).endAddress v.mesh<2^w) :
    let occ:=v.catalystPairOwners P z width
    let parity:=v.catalystPairParity P z width
    let r:=Fintype.card (Slots z d k)
    2*r≤occ.size ∧ 2*r≤parity.size ∧ occ.base+occ.size=parity.base ∧
      parity.base+parity.size=v.catalystStaticStart P z width ∧
      occ.Fits w (v.privateArena P z width).first ∧ parity.Fits w (v.privateArena P z width).first := by
  intro occ parity r
  let A:=v.privateArena P z width
  have cut := v.catalyst_static_before P z width
  have tail : A.first≤A.endAddress v.mesh:=Nat.le_add_right ..
  have next : occ.base+occ.size=parity.base:=rfl
  have last : parity.base+parity.size=v.catalystStaticStart P z width:=rfl
  have n : 2*r≤occ.size:=(Nat.lt_log2_self (n:=2*r)).le
  have m : 2*r≤parity.size:=(Nat.lt_log2_self (n:=2*r)).le
  have parityEnd : parity.base+parity.size≤A.first:=last.le.trans cut
  have occEnd : occ.base+occ.size≤A.first:=next.le.trans ((Nat.le_add_right ..).trans parityEnd)
  have fits (b : Bank) (inside : b.base+b.size≤A.first) : b.Fits w A.first :=
    ⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans (inside.trans tail)).trans_lt room,inside⟩
  exact ⟨n,m,next,last,fits occ occEnd,fits parity parityEnd⟩

theorem catalyst_static_end (ownerArea : Arena) :
    let n:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh P.catalogue P.routes F ownerArea))
    let b:=sinkBank (v.catalystStaticStart P z width) n (Fintype.card (Slots z d k)) P.catalogue.rows
    b.base+b.size=(v.privateArena P z width).first := by
  dsimp only
  rw [Slab.entries_before_install s v.mesh P.catalogue P.routes F ownerArea]
  rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
