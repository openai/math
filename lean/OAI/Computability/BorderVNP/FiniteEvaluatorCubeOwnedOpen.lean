import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostReady
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReady
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenReadback

/-! # Opening inputs on a genuine returned host memory

The host reads the initial geometry and the two physical directory columns
through the observed native history. These true words and the actual padded
source embedding suffice for the fixed host program and its concrete output
intervals. Together with the earlier geometry's marked bundle certificate
and signed controls this gives the full four-stage opening precondition.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube BorderVNP.Crossing Physical NativeIntervals HostAddress
open RoutingISA RoutingISA.Evaluator Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs VPVNP.MotifBase

variable (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ) (w : ℕ)
local notation "H" => HostScatter.Layout.fromFrame frame mem

/-- Verified numerical state of the host program and the genuine receiving-cell bounds. -/
structure HostReady : Prop where
  fits : (H).Fits w mem
  pointer : mem (frame+72)=a.hostDirectory
  banks : ∀ c<a.cells, mem (a.hostDirectory+2*c+1)=a.cellBank+c*a.cellStride
  ends : ∀ i < (H).count, ∀ side, (H).Owned mem i side →
    (H).cell mem i side < a.cells ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ a.cellStride

variable {D v n d k geometryBits J A origin m : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin a.cells) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin v) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
variable (F : Fields v a.cables n a.cells d k geometryBits σ) {x : σ → Bool} {old : Fin J → Fin v} {ports : Fin A → Fin n}
variable {il : NativeIntervals.Layout} {previous dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin m ↪o Fin il.count} {label : Fin a.cells → Label (a.n+1) a.header.d} {hz : a.header.d^(a.n+1)=il.alphabet}
variable (data : HostScatter.ResidentRows (HostScatter.Layout.fromFrame frame mem) il previous dir mem a.n a.header.d a.header.blocks a.b a.h a.K a.s)
variable (rows : PhysicalRows N cell il previous ord row Fin.valEmbedding label (productCode a.n a.header.d il.alphabet hz))
variable (interval : il.Image previous il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ a.header.blocks*(a.h*a.b))

include data rows interval cap in
/-- On the genuine distributed return, the geometry certificate is used at the
preceding profile's memory. The host-bank words are obtained from the observed
cell writer, and the real routing table's source and ordinal bounds come from
the packed slot embedding of the original crossing edge. -/
theorem host_ready_of_retention {initial written : ℕ → ℕ} (keep : HostRetention a frame initial written mem)
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^geometryBits)
    (supplyRoom : ∀ c, suppliedSize N cell c ≤ a.cellStride) {geometry : ℕ → ℕ}
    (header : Header frame origin a.cables a.cells J initial) (image : Image F old ports x origin geometry)
    (previousGeo : ∀ z, origin ≤ z → z < origin+5*a.cables → initial z=geometry z)
    (start : frame+112 ≤ origin) (before : origin+5*a.cables ≤ a.header.header)
    (words : HostWords a frame mem) (packet : (H).packets=a.header.packetBase) (single : (H).singles=a.singleBank)
    (radix : 0<a.header.d) (width : 0<a.h*a.b) (room : a.stop < 2^w)
    {controls teams : ℕ} (axis : Fin (a.n+1)) {profile : ℕ → ℕ}
    (entry : NativeEntry a frame controls axis teams profile initial written) : HostReady a frame mem w := by
  obtain ⟨scheduled,_,directory⟩ := entry.image
  have readGeo (z : ℕ) (lo : origin ≤ z) (hi : z < origin+5*a.cables) : mem z=geometry z :=
    (keep.geometry start z lo (hi.trans_le before)).trans (previousGeo z lo hi)
  have hdr := keep.header header
  have ends := host_ends_geometry a frame mem N cell aux siteID edgeID portID F rep codes fieldRoom supplyRoom hdr image readGeo
  have fit := host_fits_of_publication a frame mem N cell aux siteID edgeID portID F data rows interval cap rep codes
    fieldRoom supplyRoom hdr image readGeo before words packet single radix width room axis directory keep.banks
  exact ⟨fit,words.cells,fun c hc => by rw [Nat.mul_comm 2 c,keep.banks c hc]; exact (directory.hostRows c hc).2,ends⟩

end FiniteEvaluator.CubeAllocation

namespace RoutingISA.SignedTaskArena

open Packing BottomReports BorderVNP.Cube FiniteEvaluator

variable (t : Layout) {team frame offsets control live ports bundles b w : ℕ}
variable (owner : Fin bundles → Fin t.cube.cells) (header : Fin bundles → BottomReports.BundleHeader)
local notation "H" => t.openInputs team frame offsets control live ports bundles b owner header

/-- The host's actual readback and the signed profile's input fields yield the
two complete preconditions for both directions of the physical opening suffix. -/
theorem Layout.owned_open_ready {initial written mem : ℕ → ℕ}
    (keep : CubeAllocation.HostRetention t.cube frame initial written mem)
    (host : CubeAllocation.HostReady t.cube frame mem w)
    (fields : t.OpenFields team frame offsets control live ports bundles initial)
    (controls : ∀ i : Fin 37, initial (control+i.val)=t.controls i.val)
    (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
    (bank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (sort : BundleSort.SectionSpec room.markers owner header initial t.p.bundlePayload)
    (first : frame+112 ≤ control) (payload : control ≤ t.p.bundlePayload)
    (padding : Padding.HeaderFits w frame mem) (padFit : (Padding.Layout.fromFrame frame mem).Fits w mem) :
    OpenSuffix.Ready (H) frame mem w ∧ OpenSuffix.Placement (H) t.cube t.before frame mem := by
  have dest := CubeAllocation.host_dest t.cube frame mem host.pointer host.banks host.ends
  exact ⟨t.ready_of_resident owner header fields controls room bank sort keep.open_frame (keep.geometry first)
    payload padding padFit host.fits (fun i hi side own => (dest i hi side own).1),
    host.pointer,host.banks,host.ends,rfl,rfl,rfl,rfl⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
