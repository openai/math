import OAI.Computability.BorderVNP.DiagonalExternalSewNumericName
import OAI.Computability.BorderVNP.FiniteBottomPaidDictionary
import OAI.Computability.BorderVNP.PackedSeedBaseCaps
import OAI.Computability.BorderVNP.PackedBottomBoxScalars
import OAI.Computability.BorderVNP.PackedBankPublicReplay
import OAI.Computability.BorderVNP.PackedBankFullProgramFields
import OAI.Computability.BorderVNP.PackedHistoryNormalizedGridRoutes

/-! # Bank and scalar bounds of the routed finite-field seed

The physical field directory stores one scalar gadget per fine site, followed by
the actual fine ties and padding checks. Its single box reference and grouped
equalities give the public charge independently of the field table entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FiniteBottom

open Crossing Inherited BottomGridBank BottomReports CellAddresses GridBoxes CellSparse
open scoped Classical
open private channelVolume bound_sum from OAI.Computability.BorderVNP.PackedBottomBoxCharges

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable {F : Type*} [Field F] [Fintype F] (table : N.Tables F) (copies capFine cap : ℕ)
local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "inc" => incoming G v

omit [Field F] in
private theorem finiteBody_length (fit : GridBoxes.stride N cell v ≤ capFine)
    (room : Fintype.card {u : N.Site // cell u = v} + (capFine+inc) ≤ cap) :
    (scalarFactors N cell v siteID edgeID portID table ++
      wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine).length ≤ cap := by
  have padding := (GridPadding.factors_length_le pack v
    (channelAddress (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v capFine)).trans
    (channelVolume N cell position width owner channelID groupID v)
  simp only [wiring,scalarFactors,List.length_append,List.length_map,siteList_length,
    fineTies,List.length_ofFn,fineZeros,List.length_range]
  unfold GridBoxes.stride at fit ⊢
  omega

omit [Field F] in
/-- Resource bounds for an arbitrary finite-field fine table in its true birth program.
The scalar bound includes the published copy stride even when there are zero copies. -/
theorem finiteBorn_bankBounds (fit : GridBoxes.stride N cell v ≤ capFine)
    (room : Fintype.card {u : N.Site // cell u = v} + (capFine+inc) ≤ cap) :
    let s := finiteBorn N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
      table copies capFine fit
    s.publicNodes ≤ 1036*(1+Fintype.card (BottomRepeat.Row G v)) ∧ s.expandedLoad ≤ copies*(2*cap) ∧
      s.ScalarBound (max (max 2 (max copies cap)) (max 1 s.size)) := by
  intro s
  let box := scalarFactors N cell v siteID edgeID portID table ++
    wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine
  have length := finiteBody_length N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
    table capFine cap fit room
  have slab : capFine+inc ≤ cap := (Nat.le_add_left ..).trans room
  refine ⟨BottomRepeat.bornWith_publicNodes G channelID groupID v copies capFine (capFine+inc) box,
    BottomRepeat.bornWith_expandedLoad G channelID groupID v copies capFine (capFine+inc) box cap slab length,?_⟩
  intro a ha
  have h := BottomRepeat.bornWith_scalarBound G channelID groupID v copies capFine (capFine+inc) box le_rfl a ha
  change a.2 ≤ max 2 (max copies (max (capFine+inc) s.size)) at h
  omega

omit [Field F] in
/-- Full one-copy cost of the trivalent finite-field seed, including the stored comparison
matrix for each gadget and the resolved factor sweep of the private box. -/
theorem finiteBorn_staticNodes (fit : GridBoxes.stride N cell v ≤ capFine)
    (room : Fintype.card {u : N.Site // cell u = v} + (capFine+inc) ≤ cap)
    (degree : ∀ u, Fintype.card (FieldDirectory.Lane N u) ≤ 3) :
    (finiteBorn N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
      table copies capFine fit).staticNodes ≤ 1036*(1+Fintype.card (BottomRepeat.Row G v))+12+810487*cap := by
  let box := scalarFactors N cell v siteID edgeID portID table ++
    wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine
  have length : box.length ≤ cap := finiteBody_length N cell position pack width owner lane aligned siteID edgeID
    portID channelID groupID v table capFine cap fit room
  have mass (f : Factor) (mem : f ∈ box) : f.staticMass ≤ 81 := by
    rcases List.mem_append.mp mem with h | h
    · obtain ⟨u,_,rfl⟩ := List.mem_map.mp h
      simp only [scalarFactor,Factor.staticMass,scalarAddresses,FieldDirectory.rowIds,List.length_ofFn]
      have w := degree u.val
      have size := Nat.pow_le_pow_right (by decide : 0 < 2) w
      exact (Nat.mul_le_mul (Nat.succ_le_succ w) (Nat.succ_le_succ size)).trans (by decide)
    · simp only [wiring,List.mem_append,fineTies,List.mem_ofFn,fineZeros,List.mem_map,GridPadding.factors] at h
      rcases h with ((⟨k,rfl⟩|⟨k,_,rfl⟩)|⟨k,_,rfl⟩) <;> simp [compareUse,GridPadding.zeroFactor,Factor.staticMass]
  have static := (bound_sum box Factor.staticMass 81 mass).trans (Nat.mul_le_mul_left _ length)
  have sweep := (bound_sum box (fun f => 10000*f.staticMass) 810000
    (fun f h => Nat.mul_le_mul_left _ (mass f h))).trans (Nat.mul_le_mul_left _ length)
  apply BottomRepeat.bornWith_static_charge G channelID groupID v copies capFine (capFine+inc) box cap
  · rw [BottomRepeat.bornWith_storedMass]
    omega
  · rw [BottomRepeat.bornWith_boxMass]
    omega

end Packing.FiniteBottom

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch Shortening Packing Packing.DeckGrid Packing.PhysicalEpochs
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction GridPlacement Shortening.PreparedBins
open ParseBatch ParseBatchVerifier Prewire VPVNP Inherited BottomGridBank BottomReports
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] [Fintype K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) {R r t pins link inner n g d : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {len : Fin n} {state : Fin g}
    {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {ns ne np : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
    (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (table : (W.routedFine position).Tables K) (copies : ℕ)

/-- Use the routed grid's equality instance in the public incidence directories. -/
noncomputable local instance finiteSeedDeckEq {q l : ℕ} : DecidableEq (Fin q → Deck (l+2)) := Classical.decEq _

local notation "axes" => Fintype.card (Cube D)
local notation "V₀" => GridHosts.tileCount axes d
local notation "width₀" => fun _ : Fin V₀ => GridHosts.inputBlockWidth r n axes d
local notation "lane₀" => GridHosts.wiredLane G V₀ Fintype.card_pos
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "degree" => Fintype.card (Direction axes)
local notation "H₀" => seedChannelWidth n r axes d
local notation "cap₀" => seedBoxCapacity n r axes d degree
local notation "fineCap" => 3*seedSiteCapacity n r axes d
local notation "channels" => Shortening.PublicCapacity.Rows.edge (groupedGridRows G axes d order position copies)
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin V₀))

/-- The finite-field seed table on the schedule's published repeated grid. -/
noncomputable abbrev finiteSeedPack :=
  FiniteBottom.bottomPack K (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) table copies

/-- Actual finite-field bottom lineages with the seed frame's channel and group row names. -/
noncomputable abbrev finiteSeedPrograms :=
  FiniteBottom.bottomPrograms K (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channels groups table copies fineCap (W.seed_stride_le position)

local notation "pr" => finiteSeedPrograms W position siteID edgeID portID table copies
local notation "bottom" => finiteSeedPack W position table copies

set_option maxHeartbeats 1200000 in
/-- Both tile caps and the scalar invariant at the actual finite-field bottom. Each
physical tile uses the full cell's width and exactly the visits of its own repeated box. -/
theorem finiteSeedPrograms_bounds :
    let route := seedRoutes S G d order position copies (Pack.table bottom)
    SiteCap route (Site.Programs.bankFields pr) false (seedPublicBase degree) ∧
    SiteCap route (Site.Programs.bankFields pr) true
      (seedPublicBase degree + copies*(2*cap₀+(2*degree+1)*H₀)) ∧
    ∀ v, (pr v).program.ScalarBound (max (max 2 (max copies cap₀)) (max 1 (pr v).program.size)) := by
  intro route
  have metric (v) := FiniteBottom.finiteBorn_bankBounds (W.routedFine position) (cell position W.route) position pack₀
    width₀ order lane₀ (W.seedLane_aligned position) siteID edgeID portID channels groups v table copies fineCap cap₀
    (W.seed_stride_le position v) (show _ ≤ cap₀ from by
      change Fintype.card {u : (W.routedFine position).Site // cell position W.route u = v} +
        (fineCap + incoming (W.seedGrouped position) v) ≤ cap₀
      have h := W.seedBorn_room position v
      unfold bottomStride at h
      omega)
  let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
  have test (tile) : (fun v => reduceMove (d+1) (route.origin v) = tile) = (fun v => v = coord.symm tile) := by
    funext v
    have origin : reduceMove (d+1) (route.origin v) = coord v :=
      seed_origin S G d order position copies (Pack.table bottom) v
    exact (congrArg (· = tile) origin).trans (propext coord.eq_symm_apply.symm)
  have cells (v) :
      (pr v).program.publicNodes ≤ 1036*(2*degree+2) ∧ (pr v).program.expandedLoad ≤ copies*(2*cap₀) := by
    have card : Fintype.card (BottomRepeat.Row (W.seedGrouped position) v) ≤ 2*degree+1 :=
      seed_row_count G axes d order position copies v
    have row : 1+Fintype.card (BottomRepeat.Row (W.seedGrouped position) v) ≤ 2*degree+2 := by omega
    exact ⟨(metric v).1.trans (Nat.mul_le_mul_left _ row),(metric v).2.1⟩
  refine ⟨?_,?_,fun v => (metric v).2.2⟩
  · intro tile
    rw [test tile]
    change 1 + localRecords (seedBundle G axes d order position copies) false
      (Site.Programs.bankFields pr).prior (Site.Programs.bankFields pr).payload (fun v => v = coord.symm tile) ≤ _
    refine (congrArg (1+·) (seed_localRecords G axes d order position copies false
      (Site.Programs.bankFields pr).prior (Site.Programs.bankFields pr).payload (coord.symm tile))).le.trans ?_
    have pub := (cells (coord.symm tile)).1
    simp only [Site.Programs.bankFields,Subdivision.publicProgramData,boxCost,recordCost,Bool.false_eq_true,ite_false,seedPublicBase]
    omega
  · intro tile
    rw [test tile]
    change 1 + localRecords (seedBundle G axes d order position copies) true
      (Site.Programs.bankFields pr).prior (Site.Programs.bankFields pr).payload (fun v => v = coord.symm tile) ≤ _
    refine (congrArg (1+·) (seed_localRecords G axes d order position copies true
      (Site.Programs.bankFields pr).prior (Site.Programs.bankFields pr).payload (coord.symm tile))).le.trans ?_
    obtain ⟨pub,work⟩ := cells (coord.symm tile)
    have input := Nat.mul_le_mul_left copies (seed_capacity_le n r axes d).1
    simp only [Site.Programs.bankFields,Subdivision.publicProgramData,boxCost,recordCost,ite_true,seedPublicBase]
    nlinarith only [pub,work,input]

open private seedDegree from OAI.Computability.BorderVNP.PackedGridSeedTape

set_option maxHeartbeats 1200000 in
/-- The complete one-copy directory and all private repeated visits fit the published expanded
base budget on the same native finite-field grid, for either choice of record mode. -/
theorem finiteSeedPrograms_full_within (ex : Bool) (dB : ℕ) :
    let route := seedRoutes S G d order position copies (Pack.table bottom)
    SiteCap route (Site.Programs.fullFields pr) ex (baseMass degree cap₀ H₀ copies dB) := by
  intro route tile
  let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
  let v := coord.symm tile
  have address (u) : reduceMove (d+1) (route.origin u) = coord u :=
    seed_origin S G d order position copies (Pack.table bottom) u
  have test : (fun u => reduceMove (d+1) (route.origin u) = tile) = (fun u => u = v) := by
    funext u
    exact (congrArg (· = tile) (address u)).trans (propext coord.eq_symm_apply.symm)
  have room : Fintype.card {u : (W.routedFine position).Site // cell position W.route u = v} +
      (fineCap + incoming (W.seedGrouped position) v) ≤ cap₀ := by
    have h := W.seedBorn_room position v
    unfold bottomStride at h
    omega
  have h := FiniteBottom.finiteBorn_staticNodes (W.routedFine position) (cell position W.route) position pack₀
    width₀ order lane₀ (W.seedLane_aligned position) siteID edgeID portID channels groups v table copies fineCap cap₀
    (W.seed_stride_le position v) room (seedDegree W position)
  have card : Fintype.card (BottomRepeat.Row (W.seedGrouped position) v) ≤ 2*degree+1 :=
    seed_row_count G axes d order position copies v
  have static : (pr v).program.staticNodes ≤ 1036*(2*degree+2)+12+810487*cap₀ :=
    h.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 1036
      (show 1+Fintype.card (BottomRepeat.Row (W.seedGrouped position) v) ≤ 2*degree+2 by omega)) 12) _)
  have work : (pr v).program.expandedLoad ≤ copies*(2*cap₀) :=
    (FiniteBottom.finiteBorn_bankBounds (W.routedFine position) (cell position W.route) position pack₀
      width₀ order lane₀ (W.seedLane_aligned position) siteID edgeID portID channels groups v table copies fineCap cap₀
      (W.seed_stride_le position v) room).2.1
  rw [test]
  refine (congrArg (1+·) (seed_localRecords G axes d order position copies ex
    (Site.Programs.fullFields pr).prior (Site.Programs.fullFields pr).payload v)).le.trans ?_
  have input := Nat.mul_le_mul_left copies (seed_capacity_le n r axes d).1
  cases ex with
  | false =>
    simp only [Site.Programs.fullFields,boxCost,recordCost,Bool.false_eq_true,ite_false,Nat.add_zero,baseMass,seedPublicBase]
    omega
  | true =>
    simp only [Site.Programs.fullFields,boxCost,recordCost,ite_true,baseMass,seedPublicBase]
    nlinarith only [static,work,input]

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
