import OAI.ThreeFlat.RAM.HistoryScopeReaders

namespace OAI
/-! # The supply reader of the selected physical shrinking stage -/

namespace ThreeFlat.RAM.HistoryScopeAddress
open LinearAlgebra.SpectralBooks Diagonal Diagonal.HistoryContraction Diagonal.MotifKernel
open scoped BigOperators Classical
noncomputable section

section NativeSupply
open Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open Native.Graph PhysicalStage PhysicalShrink NavigationPass ShrinkStageNav MotifOuterTerms
set_option quotPrecheck false
open private rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
open private copiesPositive selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
attribute [local instance 2000] selectedSiteDecidableEq
variable {F Pins : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "C" => shrinkRecordState s rem A
local notation "pack" => shrinkRecordPacking s rem A
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "hc" => palette_two s
local notation "prior" => shrinkRecordWidth s rem A
local notation "key" => shrinkRecordCode s rem A
local notation "stage" => shrinkStage s D
local notation "tag" => CompressorPacking.tagBits d
local notation "pad" => PhysicalShrink.padding k d D
local notation "good" => rawConditions s rem C
local notation "order" => edgeOrder pack (baseNat (C).order) (tagOrdinal tag).toEmbedding (stage).pieces (stage).pieceRadix (shrinkPieceBound s D)
local notation "chosen" => PhysicalShrink.widths T pack prior key hc
local notation "many" => PhysicalShrink.r T pack prior key hc
local notation "tiles" => PhysicalShrink.tile T pack prior key hc
variable (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
    (ht : 0 < CompressorPacking.tagBits (2^s))
local notation "outWidths" => shrinkIssuedWords T s D rem hD small A branch
local notation "hist" => shrinkIssuedBranch T s D rem hD small A branch
local notation "lay" => ShrinkMotif.chooseWidths outWidths
local notation "padding" => tagPadding (V:=(C).Base) (L:=BitWord rem) (tagOne ht) (tagOne_ne ht) pad
local notation "G" => Resident.successor («pad»:=pad) stage pack (C).order (shrinkPieceBound s D) lay hc good ht
variable (v : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (CompressorPacking.tagBits (2^s))) (BitWord rem))
    (m : (shrinkRecordPacking s rem A).Motif)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The physical shrinking stage's supply reader on the selected history.
The remaining arguments of the reader are the two word layouts, the occupied
port and bit, the address layout and memory, and their five numerical read conditions. -/
abbrev Read.supplyField :=
  @Read.histogramAtGraph (2*d) d (C).Base (BitWord s) (BitWord tag) (BitWord rem) F Pins
    (inferInstance : Field F)
    (inferInstance : AddCommGroup (BitWord s)) (inferInstance : AddCommGroup (BitWord tag))
    (inferInstance : AddCommGroup (BitWord rem)) (inferInstance : Fintype (C).Base)
    (inferInstance : Fintype (BitWord s)) (inferInstance : Fintype (BitWord tag))
    (inferInstance : Fintype (BitWord rem))
    pack chosen many tiles hist binary_neg good lay (stage).pieces
    (copiesPositive s D hD small) order hc pad padding v m prior G

end NativeSupply

end
end ThreeFlat.RAM.HistoryScopeAddress

end OAI
