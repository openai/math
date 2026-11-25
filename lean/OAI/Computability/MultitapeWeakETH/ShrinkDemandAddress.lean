import OAI.Computability.MultitapeWeakETH.ShrinkMapRecord

/-! # Old demand addresses for child packets indexed by site ordinal -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open VPVNP BurstRAM BurstRAM.PrivateRAM Compression Compression.ShrinkMotif
open CompressorRecords DescriptorSpace PhaseRecipe PairSimulation ShrinkBlockInputs MapResidentRows NodeArguments
open scoped Classical Fin.CommRing
noncomputable section

/-- Each old site gets room for both directions of at most n slots of width at most n. -/
def packetStride : Expr := ((Expr.lit 2).mul (.header 17)).mul (.header 17)

/-- The private arguments use consecutive site ordinals. All external rank and
incidence pointers still come from the selected old-level header. -/
def demandHeader (a : ℕ) : ShrinkCD.Header :=
  let H := ShrinkCD.Published.header a .state (ordinal a) (.lit 0) packetStride (.lit 0)
  { H with fields := { H.fields with oldHalf := { H.fields.oldHalf with
      layerBase := .lit 0, layerStride := .lit 1 } } }

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
  (sel : SelectedScore.Selection B X) (base : Word w) (positions blocks n cur : ℕ)
  (mem : Memory w)
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "head" => levelStart L cur
local notation "first" => tableBase L cur (1 : Fin 6)
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "side" => SelectedFinish.chosen B X sel
local notation "T" => packedIncidence L w cur (DemandRAM.oldCount X)
local notation "plan" => ShrinkInput.plan X cut
local notation "q" => ShrinkRankSpace.Shape.collectBank plan w
local notation "rank" => ShrinkWidthArena.scatterBank T q (ShrinkRankSpace.Shape.ranks plan : Word w) (ShrinkInput.widthBase X cut)
local notation "H" => demandHeader (a i)
local notation "A" => Arena.mk 0 (2*n*n)
local notation "d" => 2^(a i)
local notation "pieces" => Compression.PackingData.pieceCount d (Shrink.colors (a i))

variable (stored : CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem)
    (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length) (p : Fin 5 → Word w)
    (owner : p 0 = ((siteIndex X v).val : Word w)) (index : p 1 = (j.val : Word w))
/-- The typed motif component of a resident directory entry. -/
def rowMotif {a g : ℕ} (Y : State a (packingLaneBits a g)) (layout : Bool) (v : MapResidentRows.Site Y)
    (j : Fin (MapResidentRows.order Y layout v).length) : Y.packingData.Motif :=
  (MapResidentRows.entry Y layout v j).1

local notation "motif" => rowMotif (g:=g) X side v j

include stored in
theorem packetStride_eval :
    packetStride.eval p (head : Word w) mem = ((2*n*n : ℕ) : Word w) := by
  have bound := stored.words.oldRoom
  have size : (Expr.header 17).eval p (head : Word w) mem = (n : Word w) := by
    change mem (((head : Word w) + ((17 : ℕ) : Word w)).val) = _
    rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact stored.words.length
  change 2 * (Expr.header 17).eval p (head : Word w) mem * (Expr.header 17).eval p (head : Word w) mem = _
  rw [size]
  push_cast
  rfl

private theorem term_count_le {endPtr count limit : ℕ} (h : endPtr + 2*count + count*10 < limit) : count ≤ limit := by omega

private theorem encodedValue {w n : ℕ} {t : Word w} (eqn : t = (n : Word w)) (small : n < 2^w) :
    t.val = n := by rw [eqn,Fin.val_cast_of_lt small]

include stored owner index in
set_option maxHeartbeats 600000 in
/-- Both the AB member scan and CD rank lookup use the external tables
written by this selected pass and the site-indexed private child frames. -/
theorem demand_heads :
    ShrinkAB.Physical.Header.Stored (a:=a i) (g:=g) X (H).fields p (head : Word w) mem q rank first 0 motif ∧
    (H).fields.oldHalf.Stored T A 0 1 p (head : Word w) mem ∧
    (H).owners.eval p (head : Word w) mem = (q) 2 ∧
    (H).thickness.eval p (head : Word w) mem = (ShrinkInput.placementBank X T cut) 11 ∧
    (plan).stop < 2^w := by
  have level := stored.words.level
  let M := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks (a i)
  have room := stored.bounds.termRoom
  change ShrinkInput.stop X cut + 2*M + M*10 < 2^w at room
  have small : (ShrinkMotifOrder.stateNumber X motif).val < M := (ShrinkMotifOrder.stateNumber X motif).isLt
  have id := (item_read B i X sel base positions blocks n cur mem stored v j p owner index).1
  have inWord : (ShrinkMotifOrder.stateNumber X motif).val < 2^w := small.trans_le (term_count_le room)
  have motifWord : ((ordinal (a i)).eval p (head : Word w) mem).val = (ShrinkMotifOrder.stateNumber X motif).val := by
    unfold rowMotif at inWord ⊢
    exact encodedValue (t:=(ordinal (a i)).eval p (head : Word w) mem) (n:=(ShrinkMotifOrder.stateNumber X (entry X side v j).1).val) id inWord
  have ab := ShrinkCD.Published.abHeader X p (head : Word w) mem motif .state (ordinal (a i)) (.lit 0)
    packetStride (.lit 0) cut T first 0 motifWord level.ids level.rankHead level.abBank rfl
  obtain ⟨owners,thick⟩ := ShrinkCD.Published.geometry X p (head : Word w) mem .state (ordinal (a i)) (.lit 0)
    packetStride (.lit 0) cut T level.vertices level.degree level.lanes level.owner level.ids
  refine ⟨⟨ab.motif,ab.lists,ab.listStride,ab.rankBase,ab.banks,ab.destination⟩,
    ⟨rfl,packetStride_eval B i X sel base positions blocks n cur mem stored p,rfl,rfl,
      level.actualOut,level.actualIn,level.width⟩,owners,thick,?_⟩
  exact (ShrinkInput.range_bounds X cut).2.2.2.trans_lt ((Nat.le_add_right ..).trans_lt ((Nat.le_add_right ..).trans_lt room))

include stored owner index in
set_option maxHeartbeats 450000 in
/-- Resolve either unsplit endpoint to the correct half and offset in a placed child's packet. -/
theorem cd_address (atD : Bool) :
    ((H).field d pieces atD).eval p (head : Word w) mem = CursorRAM.encode w
      (ShrinkOldHalves.address (a:=a i) (g:=g) X A (PortRefresh.ArgumentAddress.siteOrdinal X) motif.1
        (if atD then !(ShrinkOldHalves.cDirection X motif) else ShrinkOldHalves.cDirection X motif)) := by
  obtain ⟨ab,child,owners,thick,space⟩ := demand_heads B i X sel base positions blocks n cur mem stored v j p owner index
  have G := ShrinkCallHeader.geometry X T cut space
  have enough := stored.words.oldRoom
  have addr := ShrinkCD.field_eq X H p (head : Word w) mem motif ab G.arcFit G.bucketFit G.piecesFit
    (by omega) owners G.regions G.nrows G.cap stored.sources.old.preimages stored.sources.old.ranked
    G.degreeFit (ShrinkInput.placementBank X T cut) false stored.sources.old.thickness thick T A 0 1 child
    stored.sources.old.incidence atD
  simpa only [Nat.one_mul,Nat.zero_add] using addr

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
