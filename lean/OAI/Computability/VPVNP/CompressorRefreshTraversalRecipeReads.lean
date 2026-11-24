import OAI.Computability.VPVNP.CompressorRefreshTraversalHeadReads
import OAI.Computability.VPVNP.CompressorRefreshMapCall
import OAI.Computability.VPVNP.CompressorRefreshDiagonalFrame
import OAI.Computability.VPVNP.CompressorRefreshMapRoute

/-!
# Addresses read by the refresh diagonal, dispatch and motif map recipes

The diagonal reads two widths and two segment offsets at the selected arc. Every motif
read is in an actual incidence column, a segment column, a demand row or the admitted
term row. The bound applies even to map operands whose endpoint has zero width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalRecipeReads

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe
open OperandInputs PairSimulation.NodeArguments RefreshMapOperands NewSlots
open scoped Fin.CommRing
open private scratch_addr from OAI.Computability.VPVNP.CompressorRecordRefreshAllocation

variable {bits g t : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (A : Arena) (child parent : ℕ)
  (U V : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (start stride limit : ℕ)
  (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (I : Input)
local notation "D" => 2 ^ S.portExponent
local notation "H" => 2 ^ S.expanderExponent
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "P" => S.graph.toSlotGraph
local notation "supply" =>
  blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "Pl" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "N" => Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent
local notation "NN" => Fintype.card (State.Base Y) * 2 ^ g * 2 ^ (S.degreeExponent 0)
local notation "ok" => Expr.ReadsFrom (· < limit) pub state m
local notation "ev" => Expr.eval pub state m

private theorem indexed_lt {w : ℕ} (h i j : ℕ) (k : W w) (v : ℕ) (eqn : k = word v) (hk : v < i)
    (hj : j < h) :
    (k * word h + word j).val < i * h := by
  rw [eqn, Fin.val_add, Fin.val_mul]
  have x : (word (bits := w) v).val ≤ v := Nat.mod_le ..
  have y : (word (bits := w) h).val ≤ h := Nat.mod_le ..
  have z : (word (bits := w) j).val ≤ j := Nat.mod_le ..
  have b := (Nat.mod_le ((word (bits := w) v).val * (word (bits :=
    w) h).val) (2 ^ w)).trans (Nat.mul_le_mul x y)
  have c := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul] at c
  exact (Nat.mod_le ..).trans_lt (by omega)

private theorem row_lt {w : ℕ} (base count stride j v : ℕ) (hw : v < count) (hj : j < stride) :
    (word (bits := w) base + word v * word stride + word j).val < base + count * stride := by
  have bound := indexed_lt stride count j (word (bits := w) v) v rfl hw hj
  rw [add_assoc, Fin.val_add]
  exact (Nat.mod_le ..).trans_lt (Nat.add_lt_add_of_le_of_lt (Nat.mod_le ..) bound)

set_option maxHeartbeats 1600000 in
-- The proof unfolds the recipes for each old and new port and for each map field.
/-- Simultaneous address bound for all selected refresh recipes. The extent conditions
are the sizes of the retained native columns and of the packed refresh allocation. -/
theorem fields {fit : Fintype.card X.Base * D * 2 ^ g * D ≤ 2 ^ bits} (directory histogram : Expr)
    (data : Describes I pub state m X v P S.port_order hd supply A child parent U V
      ((Pl).scratch bits) (word (Pl).demand) (word (Pl).term))
    (heads : TraversalHeaders.InputReads pub state m limit I) (old : U.ActualColumns X m)
    (new : V.ActualColumns Y m)
    (oi : U.actualIn.val + N ≤ limit) (ow : U.width.val + N ≤ limit)
    (ni : V.actualIn.val + NN ≤ limit) (nw : V.width.val + NN ≤ limit)
    (area : (Pl).supply ≤ limit) (fitLimit : limit ≤ 2 ^ bits)
    (wide : D < 2 ^ bits) (enough : 2 + D * H ≤ stride) (dirRead : ok directory)
    (histRead : ok histogram) :
    (∀ j, ok (DiagonalFrame.fields D (refreshSlots hd (Sum.inl 0)) I j)) ∧
      (∀ j, ok (MapRoute.fields D stride I j)) ∧
      ∀ a, ok (MapCallWords.fields P hd ties stride I
        (MapCallWords.plannedHeads D H stride I directory histogram) a) := by
  let slot := ArgumentSite.portIndex D I.parent.siteOrd I.lanes
  let block := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
  have slotR : ok slot := ⟨⟨heads.parent.site, heads.lanes⟩, trivial⟩
  have blockR : ok block :=
    ⟨⟨⟨⟨heads.parent.site, heads.lanes⟩, trivial⟩, heads.lanes⟩, heads.parent.site, heads.lanes⟩
  have bv : ev block = word (DemandScan.blocks X v.1).val :=
    ArgumentSite.blockIndex_eval X v pub state m _ _ data.site data.lanes wide
  have blockLt : (DemandScan.blocks X v.1).val < (Pl).blocks := (DemandScan.blocks X v.1).isLt
  have oldAt := ArgumentAddress.field_reads_below heads.child data.childRep old oi ow
  have oldStatic := ArgumentAddress.fieldStatic_reads_below heads.child data.childRep old oi ow
  have newStatic := ArgumentAddress.fieldStatic_reads_below heads.parent data.parentRep new ni nw
  have dmBefore : (Pl).demand ≤ (Pl).supply :=
    by unfold Allocation.Plan.supply Allocation.Plan.term; omega
  have readSegment (head : Expr) (c : Fin 8) (hne : c ≠ 0) (hr : ok head)
    (value : ev head = (Pl).scratch bits c)
      (j : Fin D) (idx : Expr) (index : ok idx)
      (hi : ev idx = idWord (sites X.baseIndex (bitWordFinEquiv g)) fit (v, j)) :
      ok (.load (head.add idx)) := by
    refine ⟨⟨hr, index⟩, ?_⟩
    change (ev head + ev idx).val < limit
    rw [value, hi]
    exact (scratch_addr Pl (dmBefore.trans (area.trans fitLimit)) c hne _ (numbered _ (v,
      j)).isLt).trans_le (dmBefore.trans area)
  let diagonal := ArgumentSite.diagonal D I.parent.siteOrd I.lanes
  have dR : ok diagonal := ⟨⟨heads.parent.site, trivial⟩, slotR⟩
  have dv := ArgumentSite.diagonal_eval X v pub state m I.parent.siteOrd I.lanes data.site
    data.lanes wide fit
  have termAt (j : ℕ) (hj : j < stride) :
      ok (.load ((I.termBase.add (block.mul (.lit stride))).add (.lit j))) := by
    refine ⟨⟨⟨heads.term, blockR, trivial⟩, trivial⟩, ?_⟩
    change (ev I.termBase + ev block * word stride + word j).val < limit
    rw [data.termBase, bv]
    exact (row_lt _ _ _ _ _ blockLt hj).trans_le area
  have termHead : ok (.load (I.termBase.add (block.mul (.lit stride)))) := by
    refine ⟨⟨heads.term, blockR, trivial⟩, ?_⟩
    change (ev I.termBase + ev block * word stride).val < limit
    rw [data.termBase, bv]
    simpa only [show word (bits := bits) 0 = 0 from rfl, add_zero] using
      ((row_lt (w := bits) (Pl).term (Pl).blocks stride 0 _ blockLt (by omega)).trans_le area)
  have demandAt (e : Tie D) : ok (MapFrameFields.storedWidth (dH :=
    H) ties stride I (.inl (false, e))) := by
    refine ⟨⟨⟨heads.demand, blockR, trivial⟩, trivial⟩, ?_⟩
    change (ev I.demandBase + ev block * word t + word (ties.symm e).val).val < limit
    rw [data.demandBase, bv]
    exact (row_lt _ _ _ _ _ blockLt (ties.symm e).isLt).trans_le
      (by unfold Allocation.Plan.supply at area; exact (Nat.le_add_right ..).trans area)
  have copies : ok (MapCallWords.copies D stride I) := termAt 1 (by omega)
  have external (dir : Bool) (j : Fin D) :
      ok (.load ((if dir then I.offIn else I.offOut).add (ArgumentSite.segment D I.parent.siteOrd
        (.lit j.val)))) := by
    have idx : ok (ArgumentSite.segment D I.parent.siteOrd (.lit j.val)) :=
      ⟨⟨heads.parent.site, trivial⟩, trivial⟩
    have pos := ArgumentSite.segment_eval X v pub state m I.parent.siteOrd data.site (.lit j.val) j
      (Nat.mod_eq_of_lt (j.isLt.trans wide)) fit
    cases dir with
    | false => exact readSegment _ 5 (by decide) heads.offOut data.offOut j _ idx pos
    | true => exact readSegment _ 6 (by decide) heads.offIn data.offIn j _ idx pos
  refine ⟨?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact oldAt false slot slotR
    · exact ⟨oldAt false slot slotR, readSegment _ 1
      (by decide) heads.widthOut data.widthOut _ _ dR dv⟩
    · exact ⟨newStatic false _, readSegment _ 5 (by decide) heads.offOut data.offOut _ _ dR dv⟩
    · exact oldAt true slot slotR
    · exact ⟨oldAt true slot slotR, readSegment _ 7
      (by decide) heads.widthIn data.widthIn _ _ dR dv⟩
    · exact ⟨newStatic true _, readSegment _ 6 (by decide) heads.offIn data.offIn _ _ dR dv⟩
  · intro j; fin_cases j
    · exact termHead
    · exact slotR
    · trivial
    · trivial
  · intro a
    cases a with
    | base f =>
      rcases f with ⟨dir, e⟩ | ⟨dir, e⟩
      · cases dir with
        | false => exact oldStatic _ _
        | true => exact ⟨newStatic _ _, external (!e.1) (tieSource e)⟩
      · cases dir <;> exact newStatic _ _
    | demand e => exact demandAt e
    | payload e =>
      have hi := (finProdFinEquiv e).isLt
      have bound : e.1.val * H + e.2.val < D * H := by
        change e.2.val + H * e.1.val < D * H at hi
        rwa [Nat.mul_comm, Nat.add_comm]
      exact termAt _ (by omega)
    | copies => exact copies
    | directory => exact dirRead
    | source => exact ⟨dirRead, trivial⟩
    | target => exact ⟨⟨dirRead, trivial⟩, copies⟩
    | hist => exact histRead

end CompressorRecords.PortRefresh.TraversalRecipeReads

end VPVNP
end Computability
end OAI
