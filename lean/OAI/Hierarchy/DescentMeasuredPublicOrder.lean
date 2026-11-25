import OAI.Hierarchy.DescentPublicOperandCarrier
import OAI.Hierarchy.DescentMeasuredOperandKey
import OAI.Hierarchy.DescentPreparedRotorInputs

namespace OAI
/-! # Original chronological order of the public rotor operands in a measured matrix row -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking
open DescentFallbackItemSelect DescentStageEdgeReceipt DescentFallbackPeriod.Projected
open DescentRotorWindowArchive DescentSIMDLookup DescentCompiler
open DescentRotor DescentBaseProfile DescentResetHostSize DescentDenseHostOrder
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P V X : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m c H field n r : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (basis : Layout m) (fit : c≤ m)
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (grp : Fin groups↪ℕ)
    (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
local notation "native" => order.trans Fin.valEmbedding
local notation "pad" => vertex.trans (Fin.castLEEmb padded)
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank grp (vertex.trans Fin.valEmbedding))
local notation "L" => 2^(m-c)
local notation:max "row" s:arg e:arg => finProdFinEquiv (localAddress A native S ready digits basis (c:=c) s e)
local notation "serial" => DescentOrderedReset.grains W A.grainCount order

/-- The fixed public ROM can have arbitrary capacity on its other fields. The
signed matrix fixes the arity, old slot bound and group/fine radices. -/
def matrixConfig (sample : DescentResetPublicOperandBook.Config) (degree cap donors k field : ℕ) :
    DescentResetPublicOperandBook.Config :=
  {sample with oldDegree:=degree,oldCap:=cap,donors:=donors,fineBits:=k,fieldBits:=field}

variable (sample : DescentResetPublicOperandBook.Config)
local notation "cfg" => matrixConfig sample A.degree A.cap L k field
variable (side : Bool) (v : V) (hi : Block c)
    (x : (matrixConfig sample A.degree A.cap (2^(m-c)) k field).Data n) (grain : X↪Grain A)
local notation "key" => grain.trans serial
local notation "lo" => (cfg).oldConfig
local notation "basic" => (cfg).basic x

/-- Input facts are the scalar header, the two earlier stem words, and the
matrix just gathered from the signed window and six measured rotor columns. -/
structure MeasuredPublicRows (A : GroupStage W G q ε (Fin groups) V k) (S : AtomSchedule)
    (ready : A.StateBounds S i) (digits : Block m≃Fin groups×Block k) (basis : Layout m) (fit : c ≤ m)
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (grp : Fin groups↪ℕ)
    (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
    (sample : DescentResetPublicOperandBook.Config) (side : Bool) (v : V) (hi : Block c)
    (x : (matrixConfig sample A.degree A.cap (2^(m-c)) k field).Data n) (grain : X↪Grain A) where
  own : Fin H→Block c→Fin (2^(m-c))→ℕ
  peers : Fin H→Fin A.degree→Option (Fin H)
  marks : Fin H→Block c→Fin (2^(m-c))→Fin (2*A.cap)→Option (Live A.degree A.cap)
  ranks : Fin H→Fin (DescentSharedBookScan.width r (2^n) A.degree)→ℕ
  comparison : Fin H→Block c→Fin (2^(m-c))→Fin (2^(m-c))→Bool
  reserved : Fin H→Fin A.degree→Fin A.degree→Fin 6→Cell field
  reached : ∀u g j b,marks ((vertex.trans (Fin.castLEEmb padded)) u) g j b=signedPanel A (order.trans Fin.valEmbedding) S ready (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank grp (vertex.trans Fin.valEmbedding))) (donor digits basis fit u g j) b
  matrix : ∀j,(matrixConfig sample A.degree A.cap (2^(m-c)) k field).oldData x j=RootSources.paddedRow own peers marks ranks comparison reserved ((vertex.trans (Fin.castLEEmb padded)) v) hi (ix j)
  signedFits : DescentSignedCableCodec.width A.degree A.cap≤field
  host : ((matrixConfig sample A.degree A.cap (2^(m-c)) k field).oldConfig.header ((matrixConfig sample A.degree A.cap (2^(m-c)) k field).basic x) 3).val=DescentResetStemWord.hostCode
    (compress (hostDomain A vertex v) (vertex v).val) (decide (v∉A.near v))
  located : ∀e,Located A digits basis v hi side (grain e)
  groupWord : ∀e,((matrixConfig sample A.degree A.cap (2^(m-c)) k field).oldConfig.digit ((matrixConfig sample A.degree A.cap (2^(m-c)) k field).basic x) (finProdFinEquiv (localAddress A (order.trans Fin.valEmbedding) S ready digits basis (c:=c) side (grain e))) 0).val=
    compress (groupDomain digits basis fit v hi) (A.pos (W.graph.src (grain e).1)).1.val
  fineWord : ∀e,((matrixConfig sample A.degree A.cap (2^(m-c)) k field).oldConfig.digit ((matrixConfig sample A.degree A.cap (2^(m-c)) k field).basic x) (finProdFinEquiv (localAddress A (order.trans Fin.valEmbedding) S ready digits basis (c:=c) side (grain e))) 1).val=(A.block (W.graph.src (grain e).1)).val

variable (obs : MeasuredPublicRows (r:=r) (field:=field) (n:=n) A S ready digits basis fit order grp vertex padded sample side v hi x grain)

include obs in
/-- Slot and grain ties are sorted by the original source chronology. -/
theorem public_operand_order (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order) (a b : X) :
    DescentFallbackItemSelect.before ((cfg).oldItem x side) (row side (grain a)) (row side (grain b)) ↔ key a<key b := by
  have code (z : Fin L×Fin (2*A.cap)) : (lo).packet basic (.inr (.inl z))=
      DescentFallbackPeriod.inputs (field:=field) (r:=r) (n:=n) obs.own obs.peers obs.marks obs.ranks (pad v) hi
        (.inr (.inl z)) := by
    have got:=obs.matrix (.inl (.inr z))
    let pkt:=DescentFallbackPeriod.inputs (field:=field) (r:=r) (n:=n)
      obs.own obs.peers obs.marks obs.ranks (pad v) hi
    exact got.trans (congrArg (observed pkt (obs.comparison (pad v) hi) (obs.reserved (pad v)))
      (ix.symm_apply_apply (.inl (.inr z))))
  have actual (e : X) : ((cfg).oldItem x side (row side (grain e))).key=
      ⟨sourceDigit A digits basis fit vertex v hi (grain e),(outgoingSlot A S ready order (grain e)).val,
        (grain e).2.val⟩ := by
    let loc:=localAddress A native S ready digits basis (c:=c) side (grain e)
    have socket := (congrArg (fun z : Fin L×Fin (2*A.cap) => (lo).packet basic (.inr (.inl z)))
      (finProdFinEquiv.symm_apply_apply loc)).trans (code loc)
    refine ((cfg).oldItem_key x side (row side (grain e))).trans ?_
    refine (congrArg (fun raw => DescentMeasuredOperandKey.key A.degree A.cap k side raw ((lo).header basic 3)
      ((lo).digit basic (row side (grain e)) 0) ((lo).digit basic (row side (grain e)) 1)) socket).trans ?_
    exact DescentMeasuredOperandKey.key_in_packet A S ready digits basis fit native grp vertex pad
      obs.own obs.peers obs.marks obs.ranks obs.reached obs.signedFits side (grain e) v hi (obs.located e)
      _ _ _ obs.host (obs.groupWord e) (obs.fineWord e)
  apply chronological key (fun e=>row side (grain e)) ((cfg).oldItem x side) _ a b
  intro i j
  refine (iff_of_eq (congrArg₂ DescentFallbackItemSelect.Key.before (actual i) (actual j))).trans ?_
  exact (scope_before A S ready digits basis fit vertex v hi ready.coordinates indexed order sorted side _ _
    (obs.located i) (obs.located j)).symm

include obs in
/-- A genuine public rotor tap accepts the earlier grain precisely at its
assigned layer and digit, using the same sparse-endpoint rows as the matrix. -/
theorem public_accepts_old [Fintype X] {h u : ℕ} (board : NonlinearExpanders.Graph n h)
    {hp : 0<(cfg).packetWidth} {src dst : X→Fin (2^n)} {pay : ℝ}
    (P₀ : BaseCircuit F board (cfg).multiplicity (cfg).packetWidth u hp src dst pay)
    (root : DescentResetLocalRoster.code (cfg).residual) (req : DescentRotorOperandQueryROM.Shape.Mouth n)
    (slot : X↪Fin (lo).count) (placed : ∀e,slot e=row side (grain e))
    (read : ∀e,(cfg).endpoints side root x (slot e)=some (src e,dst e))
    (miss : ∀j,(¬∃e,slot e=j)→(cfg).endpoints side root x j=none)
    (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order) (mass : (cfg).traffic x side root=matrixOfBundles src dst)
    (depth : DescentRecordedRotorLayers.layers n (cfg).packetWidth (cfg).gain (((cfg).reg x) 0).val=P₀.layers) (e : X) :
    (cfg).accepts x side root req (slot e)=true ↔
      ((if req.pin then dst e else src e)=req.vertex ∧
      (P₀.choose (Ordered.orderedAddress key src dst hp e).1).val=req.layer ∧
      (Ordered.orderedAddress key src dst hp e).2.val=req.digit) := by
  apply DescentResetPublicOperandBook.Config.accepts_old board (cfg) P₀ key x side root req slot read miss _ mass depth e
  intro a b
  rw [placed a,placed b]
  exact public_operand_order A S ready digits basis fit order grp vertex padded sample side v hi x grain obs indexed sorted a b

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
