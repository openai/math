import OAI.Computability.BorderVNP.PackedBundleRoutingReturn
import OAI.Computability.BorderVNP.PackedBundleHeaderFit
import OAI.Computability.BorderVNP.PackedSparseArgumentControls

/-! # The marked bundle sort in the signed joint geometry return

The signed emitter first publishes routing and private placement views, then
the 37 task controls. Its remaining geometry can place further words before
and after the two marked bundle banks. The positions and six original words
of each retained header are identified from that one physical profile and the
actual placement and receiving-cell memory images.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA GeometryFrameEncoding ParseBatchSort
open Packing BottomReports BundleSort RoutingOutputs Crossing CellAddresses CellAddressCircuit
open CellAddressPhysical CellPacketGeometry Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport

variable {S Z : Type*} [Fintype S] [Fintype Z] {s edges n d k w W J A b q o D : ℕ}
variable (banks : CellBanks.Layout) (F : Fields s edges n banks.cells d k w (S ⊕ Bool)) (hk : k ≤ w)
variable (old : Fin J → Fin s) (ports : Fin A → Fin n) (desc gap : ℕ) (shape : Fin J → Shape)
variable (valid : Frame (S ⊕ Bool) Unit) (first : Frame (S ⊕ Bool) (Fin q × Fin w))
variable (rest : Frame (S ⊕ Bool) (Outputs o w)) (sewn : Frame Z S)
variable (primary : Fin 28 → Fin (2^w)) (extra : Fin 9 → Fin (2^w)) (input : Z → Bool)
variable (origin : ℕ) (profile : Memory W) (width : w ≤ W)
include width

/-- A word-addressed portion of the signed profile output contains the two
sort banks of the six original bundle scalars, after all 37 controls and
the preceding geometry words. The routing image is from the same output. -/
theorem profile_headerBanks :
    let headers := withHeaderBanks banks F b old desc gap shape valid rest
    let suffix := GeometryOutput.prepend first headers
    let emit := controlEmitter F hk old ports (withControls extra suffix) sewn primary
    let dest := controlsBase origin edges banks.cells J A+37+q
    let x := (withSewnFields sewn).eval input
    let up := geometryHeaders F old desc (bankConfig banks gap valid) shape
    (∀ i, readings profile (origin+i.val)=value (fun j => emit.eval input (i,j))) →
      Image F old ports x origin (readings profile) ∧
      ∀ i : Fin (2^b+2^b), readings profile (dest+i.val)=value (fun j => (geometry (source banks.cells b up)).eval x (.inl (i,j))) := by
  intro headers suffix emit dest x up words
  obtain ⟨image,_,_⟩ := profile_controls F hk old ports (withControls extra suffix) sewn primary input origin profile width words
  obtain ⟨_,_,tail⟩ := sparse_argument_controls F hk old ports suffix sewn primary extra input origin profile width words
  refine ⟨image,fun i => ?_⟩
  have raw := tail (Fin.natAdd q (i.castAdd o))
  simpa only [suffix,headers,withHeaderBanks,GeometryOutput.prepend_rest,GeometryOutput.prepend_first,
    Fin.val_natAdd,Fin.val_castAdd,headerBanks,Frame.select_eval,Nat.add_assoc,dest,up,x] using raw

variable {P : Type} [Fintype P] {bits : P → ℕ} {N M : Network D P bits}
variable (retain : Retains N M) (cell : M.Site → Fin banks.cells) (aux : M.Site → ℕ)
variable (siteID : M.Site ↪ Fin s) (edgeID : M.Edge ↪ Fin edges) (portID : P ↪ Fin n)
variable (original : Fin J → N.Site) (live : Fin A → P)

/-- The actual signed profile output, native private-prefix image, and native
cell-bank directory determine the marker ranks and the ordered six-word header
groups. The absolute header slot fits by the real cell's reserved input width. -/
theorem profile_header_sections (frame : ℕ) (placed mid : ℕ → ℕ)
    (rect : banks.cells+6*J+banks.cells ≤ 2^b) (keysFit : banks.cells < 2^k)
    (positionsFit : 2^b ≤ 2^w) (fitBanks : banks.Fits w)
    (descFit : desc < 2^w) (scanFit : 2^Nat.clog 2 J*desc < 2^w) (copies : ∀ i, (shape i).copies < 2^w)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^w)
    (codes : ∀ c, (F.cells c).val=c.val)
    (room : ∀ c, guessedSize M cell c+siteSize M cell c aux+suppliedSize M cell c < 2^w) :
    let x := (withSewnFields sewn).eval input
    let host := fun i => retain.site (original i)
    let old := siteID ∘ host
    let l := privateLayout frame origin edges banks.cells J desc gap
    let after := banks.written mid banks.cells
    let hs := fun i => geometryHeader retain siteID F (x:=x) l after banks.dest original i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    let headers := withHeaderBanks banks F b old desc gap shape valid rest
    let suffix := GeometryOutput.prepend first headers
    let emit := controlEmitter F hk old (portID ∘ live) (withControls extra suffix) sewn primary
    let dest := controlsBase origin edges banks.cells J A+37+q
    CellAddressPhysical.Represents M cell aux siteID edgeID portID F x →
    l.Image (readings profile) J placed → l.Fits w (readings profile) →
    (∀ i : Fin J, mid (l.raw+2*i.val)=placed (l.raw+2*i.val) ∧ mid (l.raw+2*i.val+1)=placed (l.raw+2*i.val+1)) →
    (l.raw+2*J ≤ banks.dest ∨ banks.dest+2*banks.cells ≤ l.raw) →
    (∀ c : Fin banks.cells, readings profile (l.supplied+c.val)+gap+
      PrivatePlacement.prefixCounts (l.owner (readings profile)) desc J c.val ≤ banks.stride) →
    (∀ i, readings profile (origin+i.val)=value (fun j => emit.eval input (i,j))) →
      SectionSpec rect (cell ∘ host) hs (readings profile) dest := by
  intro x host old l after hs headers suffix emit dest net place fit keep apart capacity words
  obtain ⟨image,sort⟩ := profile_headerBanks banks F hk old (portID ∘ live) desc gap shape valid first rest sewn
    primary extra input origin profile width words
  apply SectionSpec.of_cellBanks retain banks cell aux siteID edgeID portID F net codes room frame origin desc gap original
    live valid shape (readings profile) placed mid (readings profile) dest rect keysFit positionsFit
    (fun c => bankConfig_fits banks fitBanks gap (by have h := capacity c; omega) c) descFit scanFit copies stride image place fit keep apart _ sort
  intro i
  exact bankHeader_fits banks l fitBanks (readings profile) placed mid fit rfl place keep apart capacity i _ _ _ _ _

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
