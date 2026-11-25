import OAI.Computability.BorderVNP.PackedBundleGeometryOperands
import OAI.Computability.BorderVNP.PackedBundleSortPhysical
import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # Identifying the sorted header source with the actual native placement

The public circuit reads final owner and staging columns, computes private displacements,
and sorts the six fields. Its values coincide with the private-placement RAM image even
when the two operations are different blocks of the common reconstruction program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Diagonal.ExternalSew
open VPVNP.VerifierNetwork ParseBatchSort PackedHistogram CellPacketGeometry
open private retained from OAI.Computability.BorderVNP.PackedBundleGeometryOperands

variable {D s m n C d k w J : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Original-row public header program, prior to marker insertion and stable sorting. -/
noncomputable def geometryHeaders (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w))
    (shape : Fin J → Shape) : Frame σ (Pins J k w) :=
  headerFrame F.cells shape (geometryOperands F old desc cfg)

variable {N M : Network D P bits} (retain : Retains N M)
variable (cell : M.Site → Fin C) (aux : M.Site → ℕ) (siteID : M.Site ↪ Fin s)
variable (edgeID : M.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {x : σ → Bool} (net : Represents M cell aux siteID edgeID portID F x)
variable (code : ∀ c, (F.cells c).val = c.val)
variable (fit : ∀ c, guessedSize M cell c+siteSize M cell c aux+suppliedSize M cell c < 2^w)

include net code fit

/-- The scalar fields and owner of the actual circuit agree with the header read
from the real placement and retained-site view. Its relative address was constructed
from the original owner scan, so there is no read dependency on the prefix pass. -/
theorem geometryHeaders_values (l : PrivatePlacement.Layout) (before placed after : ℕ → ℕ)
    (run : l.Image before l.entries placed) (layoutFit : l.Fits w before)
    (keep : ∀ i : Fin l.entries, after (l.raw+2*i.val) = placed (l.raw+2*i.val) ∧
      after (l.raw+2*i.val+1) = placed (l.raw+2*i.val+1))
    (receive : ℕ) (origin : Fin l.entries → N.Site) (cfg : Frame σ (Config C w))
    (shape : Fin l.entries → Shape)
    (owners : ∀ i, l.owner before i.val = (cell (retain.site (origin i))).val)
    (supplied : ∀ c : Fin C, before (l.supplied+c.val) = suppliedSize M cell c)
    (config : ∀ c : Fin C, value (fun j => cfg.eval x (.inl (c,j))) = after (receive+2*c.val+1)+l.gap)
    (desc : l.desc < 2^w) (scanRoom : 2^Nat.clog 2 l.entries*l.desc < 2^w)
    (copies : ∀ i, (shape i).copies < 2^w)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^w) :
    let host := fun i => retain.site (origin i)
    let old := siteID ∘ host
    let headers := fun i => geometryHeader retain siteID F (x:=x) l after receive origin i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    (∀ i, (headers i).siteSlot < 2^w) →
    (∀ i, value (fun j => (geometryHeaders F old l.desc cfg shape).eval x (.inl (i,.inl j))) = (cell (host i)).val) ∧
    ∀ i f, value (fun j => (geometryHeaders F old l.desc cfg shape).eval x (.inl (i,.inr (f,j)))) =
      scalar (headers i) f := by
  intro host old headers room
  let up := geometryOperands F old l.desc cfg
  have pin (i : Fin l.entries) :
      value (fun j => up.eval x (.inl (i,.inl j))) = (F.cells (cell (host i))).val := by
    simpa only [up,geometryOperands_owner,Function.comp_def,old] using net.owner (host i)
  refine ⟨fun i => ?_, fun i f => ?_⟩
  · simpa only [geometryHeaders,headerFrame_key] using (pin i).trans (code _)
  · let c := cell (host i)
    let ptr := after (receive+2*c.val+1)
    let amount := suppliedSize M cell c
    let off := PrivatePlacement.prefixCounts (l.owner before) l.desc i.val (l.owner before i.val)
    let base := value (fun j => (CellAddressViews.frame F).eval x (.inr (.inl (old i)),j))
    have relative : value (fun j => up.eval x (.inl (i,.inr (false,j)))) = off :=
      geometryOperands_prefix F old l.desc cfg x (l.owner before)
        (fun a => (net.owner _).trans ((code _).trans (owners a).symm)) desc scanRoom i
    have address : (headers i).siteSlot = ptr+l.gap+amount+off := by
      change (rawHeader after l.raw receive i.val (shape i).copies base (shape i).fine (shape i).incoming
        (shape i).cap).siteSlot = _
      simp only [rawHeader,(keep i).1,(keep i).2,run.owner_eq layoutFit i.isLt,run.slots i.val i.isLt,owners i,supplied]
      dsimp [ptr,amount,off,c,host]
      rw [owners i]; omega
    have absRoom : ptr+l.gap+amount+off < 2^w := address ▸ room i
    have fetch := geometryOperands_receive F old l.desc cfg x c (ptr+l.gap) amount (config c)
      (SuppliedOffsets.cell_size M cell aux siteID edgeID portID F net fit c) (by omega)
    have stage : value (fun j => up.eval x (.inl (i,.inr (true,j)))) = base := by simp only [up,retained,base]
    have out := headerFrame_value F.cells shape up x i c (pin i) off base (ptr+l.gap+amount)
      relative stage fetch absRoom (copies i) (stride i) f
    have headerEq : (shape i).header (ptr+l.gap+amount+off) base = headers i := by
      rw [←address]; rfl
    exact out.trans (congrArg (fun h => scalar h f) headerEq)

variable {A b : ℕ}

/-- The private prefix and routing image of the same run identify the entire sorted
section with the six true geometry headers per retained site. The stable-sort output
may occur inside a larger shared geometry advice block. -/
theorem SectionSpec.of_geometryHeaders (head origin receive desc gap : ℕ)
    (original : Fin J → N.Site) (live : Fin A → P) (cfg : Frame σ (Config C w)) (shape : Fin J → Shape)
    (before placed after mem : ℕ → ℕ) (dest : ℕ) (rect : C+6*J+C ≤ 2^b)
    (keysFit : C < 2^k) (positionsFit : 2^b ≤ 2^w)
    (config : ∀ c : Fin C, value (fun j => cfg.eval x (.inl (c,j))) = after (receive+2*c.val+1)+gap)
    (width : desc < 2^w) (scanRoom : 2^Nat.clog 2 J*desc < 2^w) (copies : ∀ i, (shape i).copies < 2^w)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^w) :
    let host := fun i => retain.site (original i)
    let old := siteID ∘ host
    let l := RoutingOutputs.privateLayout head origin m C J desc gap
    let hs := fun i => geometryHeader retain siteID F (x:=x) l after receive original i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    let up := geometryHeaders F old desc cfg shape
    RoutingOutputs.Image F old (portID ∘ live) x origin before → l.Image before J placed → l.Fits w before →
    (∀ i : Fin J, after (l.raw+2*i.val) = placed (l.raw+2*i.val) ∧
      after (l.raw+2*i.val+1) = placed (l.raw+2*i.val+1)) →
    (∀ i, (hs i).siteSlot < 2^w) →
    (∀ i : Fin (2^b+2^b), mem (dest+i.val) =
      value (fun j => (geometry (source C b up)).eval x (.inl (i,j)))) →
    SectionSpec rect (cell ∘ host) hs mem dest := by
  intro host old l hs up geom run layoutFit keep room result
  have facts := geom.placed M cell aux siteID edgeID portID F net code fit host live origin before
  have owner (i : Fin J) : l.owner before i.val = (cell (host i)).val := by
    simpa only [l,RoutingOutputs.privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm i.val 2]
      using congrArg Prod.fst (facts.1 i)
  have supplied (c : Fin C) : before (l.supplied+c.val) = suppliedSize M cell c := by
    simpa only [l,RoutingOutputs.privateLayout,PrivatePlacement.Layout.supplied,RoutingOutputs.bases,Nat.mul_comm 2 m]
      using facts.2.1 c
  obtain ⟨keys,values⟩ := geometryHeaders_values F retain cell aux siteID edgeID portID net code fit
    l before placed after run layoutFit keep receive original cfg shape owner supplied config width scanRoom copies stride room
  exact SectionSpec.of_words up x (cell ∘ host) hs rect keysFit positionsFit keys values mem dest result

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
