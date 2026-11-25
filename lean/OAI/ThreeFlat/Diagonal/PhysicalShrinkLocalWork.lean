import OAI.ThreeFlat.Diagonal.PhysicalShrinkElectedPrice
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal

namespace OAI
/-! # Typed fresh cost of the canonical binary shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression CompressorPacking PhysicalShrink HistoryContraction MotifKernel
open MotifOuterTerms
open scoped Classical BigOperators
open private fibre_sum_instances from OAI.ThreeFlat.Diagonal.PhysicalShrinkElectedPrice
open private cpos from OAI.ThreeFlat.Diagonal.PhysicalStageShrink
noncomputable section

variable {F Pins : Type} [Field F] [Fintype F]

private def shrinkBound {d l D m : ℕ} {A : State d l} (R : Move F A D m) (J : R.Assembler Pins)
    (C : R.ShrinkSiteCopies) (coefficient limit : ℕ) : Prop :=
  ∀ (L : A.Words Pins) (t : Fin R.rules.count) (prev : A.Site→ℕ),
    (∀ x,1+A.incidentWidth x≤prev x) → ∀ x,
      1+(R.next t).incidentWidth x+C.copies t x≤limit →
      (J L t).stage.freshResources ((Equiv.cast (congrArg Shape.Site (R.target_eq t))).symm x)≤
        coefficient*R.push t (fun y=>1+(R.next t).incidentWidth y+C.copies t y) prev x

omit [Fintype F] in
private theorem shrinkBound_degree {d l D D' m : ℕ} {A : State d l} (e : D=D')
    (R : Move F A D m) (J : R.Assembler Pins) (C : R.ShrinkSiteCopies) {k V : ℕ}
    (h : shrinkBound R J C k V) :
    shrinkBound (e ▸ R) (Move.castAssembler e R J) (copiesDegree e R C) k V := by cases e; exact h

omit [Fintype F] in
private theorem shrinkBound_lanes {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (C : R.ShrinkSiteCopies) {k V : ℕ}
    (h : shrinkBound R J C k V) :
    shrinkBound (Move.recastInputLanes e A R) (Move.inputAssembler e A R J) (copiesLanes e A R C) k V := by
  cases e
  exact h

namespace Block

variable (B : Block F) (level : Fin B.levels)
local notation "s" => B.exponent level.val
local notation "d" => 2^s
local notation "c" => 2*d+1
local notation "D" => 2^B.exponent (level.val+1)
local notation "T" => B.shrink
variable (W V : ℕ)
    (bitCaps : ∀ k : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row k)).bitCap≤V)
    (fitsWord : V*max 1 V≤2^W)

include bitCaps fitsWord

attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin motifNumbers demandWidth PhysicalShrink.picked
attribute [local irreducible] shrinkingGraph SlotRefinement.actualWidth allPieceSlots
  ShrinkMotif.chooseWidths PhysicalShrink.r Owner.childOrder Local.assemblyOrder shrinkSite


set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
omit [Fintype F] in
private theorem shrinkMove_bound {lanes rem hbits tags : ℕ} (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord c × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d c)
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<d) (hD : 0<D)
    (small : ((2^c*d*d:ℕ):ℝ)/((D : ℕ):ℝ)≤1/1024) (tagSize : 1<2^tags)
    (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d c ↪ ℕ)
    (order : ShrinkEdge P (parallel c d D) ↪ ℕ) :
    shrinkBound (shrinkMove T A u P agree good hd hD small tagSize code order)
      (shrinkMove_assembler (Pins:=Pins) T A u P agree good hd hD small tagSize code order)
      (shrinkMove_siteCopies T A u P agree good hd hD small tagSize code order)
      (B.localCoefficient*(W+1)^3) V := by
  unfold shrinkMove_assembler shrinkMove_siteCopies
  apply shrinkBound_degree (e:=degree_eq (cpos hd) hd hD)
  intro L idx prev previous v atSite
  have hc : 2≤c := cpos hd
  let old:=oldWidth A u
  let n:=parallel c d D
  let pad:=padding c d D
  let tag:=Native.adjacentMask tagSize
  have nz:=Native.adjacent_ne tagSize
  let base:=widths T P old code hc
  let many:=r T P old code hc
  let tiles:=tile T P old code hc
  let hist:=(Fintype.equivFin (shrinkBranches T A u P hd code)).symm
  let lay:=ShrinkMotif.chooseWidths (issued T P old code hc (hist idx))
  let G:=CompressorRefresh.union (shrinkingGraph P lay n order hc binary_neg good)
    (tagPadding tag nz pad)
  let w:=outputWidth P base many tiles (hist idx) binary_neg good lay n order hc pad
  let X : State (usedDegree n c d+pad) rem :=
    {Base:=A.Base×BitWord tags, order:=productOrder A.order (Native.tagOrdinal tags),
     Site:=Site A.Base (BitWord tags) (BitWord rem),chart:=Equiv.prodAssoc _ _ _,graph:=G,width:=w}
  let fresh:=shrinkWordLayout (Pins:=Pins) P base many tiles hist binary_neg good n order hc pad (tagPadding tag nz pad) idx
  let I := StageAddress.shrinkInputIso A.graph A.chart u P agree A.width
  let fibre := {x : A.Site // P.placement lay (I.site x)=v}
  have enumerated : Local.activeCopiesAt P lay many v=∑ a : Active (partySite P lay) v,many a.val := by
    unfold Local.activeCopiesAt
    exact fibre_sum_instances (fun a : Active (partySite P lay) v => many a.val)
  have copyCharge := congrArg (fun copies : ℕ => 1+X.incidentWidth v+copies) enumerated
  have billed := B.paid_packed_shrink level W V bitCaps fitsWord A u P agree good hd hD small tagSize code order
    L idx prev v (X.incidentWidth v) previous (copyCharge.symm.le.trans atSite) (X.words_incidentWidth fresh v)
  refine billed.trans_eq (congrArg (fun total => (B.localCoefficient*(W+1)^3)*total) ?_)
  exact congrArg₂ Nat.add copyCharge.symm (fibre_sum_instances (fun a : fibre => prev a.val))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
omit [Fintype F] in
private theorem shrinkBinary_bound (rem : ℕ) (hD : 0<D) (small : ((2^c*d*d:ℕ):ℝ)/((D : ℕ):ℝ)≤1/1024)
    (A : State d (shrinkCharge s+rem)) :
    shrinkBound (shrinkBinary T s D rem hD small A) (shrinkBinary_assembler (Pins:=Pins) T s D rem hD small A)
      (shrinkBinary_siteCopies T s D rem hD small A) (B.localCoefficient*(W+1)^3) V := by
  unfold shrinkBinary_assembler shrinkBinary_siteCopies
  apply shrinkBound_lanes
  unfold shrinkRaw_assembler shrinkRaw_siteCopies
  apply shrinkMove_bound B level W V bitCaps fitsWord

local notation "move₀" => shrinkBinary T s D
local notation "words₀" => shrinkBinary_assembler (Pins:=Pins) T s D
local notation "charge₀" => shrinkBinaryCharge T s D

omit [Fintype F] in
/-- At a selected successor, its actual chronological charge bounds each active
motif's sorter height. The original physical fibre supplies precisely the previous
width mass needed by the typed shrink assembly. -/
theorem shrink_fresh_to_push (rem : ℕ) (hD : 0<D) (small : ((2^c*d*d:ℕ):ℝ)/((D : ℕ):ℝ)≤1/1024)
    (A : State d (shrinkCharge s+rem)) (L : A.Words Pins) (t : Fin (move₀ rem hD small A).rules.count)
    (prev : A.Site→ℕ) (previous : ∀ x,1+A.incidentWidth x≤prev x)
    (x : ((move₀ rem hD small A).next t).Site) (atSite : charge₀ rem hD small A t x≤V) :
    ((words₀ rem hD small A) L t).stage.freshResources
      ((Equiv.cast (congrArg Shape.Site ((move₀ rem hD small A).target_eq t))).symm x) ≤
      (B.localCoefficient*(W+1)^3)*(move₀ rem hD small A).push t (charge₀ rem hD small A t) prev x :=
  shrinkBinary_bound (Pins:=Pins) B level W V bitCaps fitsWord rem hD small A L t prev previous x atSite


end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
