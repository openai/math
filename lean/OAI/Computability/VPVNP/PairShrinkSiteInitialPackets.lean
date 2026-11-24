import OAI.Computability.VPVNP.PairShrinkFirstMapMemory
import OAI.Computability.VPVNP.PairShrinkPackedPackets
import OAI.Computability.VPVNP.PairShrinkSiteBank
import OAI.Computability.VPVNP.PairShrinkRoleChildTyped

/-!
# Resident operands after the shrinking site's two field scans

The ordered children and once-guessed absorbed fields produce the entry
memory of every map at the site. The old row pointers and the popped
parent pointer lie in different layers. All their argument words precede
the histogram, so the two scans preserve the parent packet while storing
the children's independent halves and the hidden bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkBlockInputs CompressorRecords.ShrinkSlots
open NodeArguments NodeArguments.ChildScan DFS LocalHistory
open scoped Fin.CommRing

variable {K : Type} {R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
variable (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g w : ℕ}
variable (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
private noncomputable abbrev siteTerm := (B.shrinkPassAt f hf i rfl X).step.term sel
private noncomputable abbrev siteParser := (shrinkPassReaders B f hf i rfl X).termParsers sel
local notation "reader" => siteParser B f hf i X sel
variable (workspace : Word w) (positions blocks cur : ℕ)
variable (sp : ShrinkResidentSources.Bounds B i X workspace positions blocks cur)
variable (n rowEnd older later limit : ℕ)
variable (v : (X.Base × BitWord (packingTagBits (2 ^ a i))) × BitWord g)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
  X.packingInputIso.site.symm) X.network.Half v)
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
variable (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v)
local notation "J" => jobs B i X sel workspace positions blocks cur sp n rowEnd older later
  v old parent q
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n rowEnd
  (Fintype.card B.Entry)
local notation "parentNode" => later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal Y v
local notation "parentPacket" => Packet.mk parentNode (packed Y v parent)
local notation "hiddenRows" => ShrinkHiddenSlots.rows X side widths v hidden
local notation "upper" => ShrinkCallABI.hiddenBase regions n
local notation "keys" => ShrinkHistoryRows.hiddenOrder X
local notation "ptr" => childNode X older B.recordLimit

private theorem child_injective : Function.Injective (childNode X older B.recordLimit) := by
  intro u u' eqn
  apply (siteOrder X).entries.symm.injective
  apply Fin.ext
  change older + (B.recordLimit + 2) * ((siteOrder X).entries.symm u).val =
    older + (B.recordLimit + 2) * ((siteOrder X).entries.symm u').val at eqn
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < B.recordLimit + 2) (Nat.add_left_cancel eqn)

private theorem packed_move {d l : ℕ} (Z : State d l) {u u' : Z.network.Site} (e : u = u')
    (h : Z.network.Half u) : packed Z u' (e ▸ h) = packed Z u h := by
  cases e
  rfl

set_option maxHeartbeats 1000000 in
-- The parent packet transports the half through the resident equality of sites.
private theorem parent_eq :
    Packet.mk (J).node (packed Y _ (J).parent) = parentPacket := by
  exact congrArg₂ Packet.mk
    (node_eq B i X sel workspace positions blocks cur sp n rowEnd older later v old parent q)
    (packed_move Y q.2.symm parent)

set_option maxHeartbeats 2400000 in
-- The packet readbacks identify the dependent old and successor halves of the selected term.
/-- In the physical store of the two parsed lists, every operand and the popped parent agree
with the canonical resident job. The argument bounds hold through the end of each node slot. -/
theorem initialPackets (priv : Word w → Word w) (xs : List (Child X))
    (es : List ShrinkHiddenGuess.Row)
    (encodedOld : children (t := siteTerm B f hf i X sel) X v ((reader).order.children v) old = xs)
    (encodedHidden : hiddenRows = es)
    (space : ShrinkCanonicalJob.PacketSpace B i X sel q.1.1 q.1.2 J n limit)
    (oldNodes : ∀ u, ptr u < rowEnd) (parentNodeFit : parentNode < rowEnd)
    (earlier : ∀ u, ptr u < parentNode) (wire : X.maxWireWidth ≤ n)
    (present : (parentPacket).Stored (regions).arguments (scratch n priv))
    (size : ∀ m t, widths m (!side, t) ≤ n ^ 2)
    (room : upper + (keys).length * n ^ 2 ≤ 2 ^ w) :
    let packets := xs.map (Child.packet X older B.recordLimit)
    let after := ShrinkHiddenGuess.storeRows upper (n ^ 2) es
      (storePackets (regions).arguments packets priv)
    (J).Packets n after ∧ (J).ChildWords after n ∧
      ShrinkCallSupplyCells.Absorbed X side widths q.1.1 q.1.2 (J).scratch (q.2.symm ▸ hidden)
        after ∧
      (∀ u, (J).arena.base ((J).nodes u) + (J).arena.stride ≤ (J).scratch.hist) ∧
      (J).arena.base (J).node + (J).arena.stride ≤ (J).scratch.hist := by
  rw [← encodedHidden]
  intro packets after
  have nodes (u) : ptr u = (J).nodes u :=
    ShrinkOldHalves.Physical.childNode_eq X older B.recordLimit u
  have node : (J).node = parentNode :=
    node_eq B i X sel workspace positions blocks cur sp n rowEnd older later v old parent q
  have kidsLow (u) : (J).arena.base ((J).nodes u) + (J).arena.stride ≤ (J).scratch.hist :=
    (regions).node_before (nodes u ▸ oldNodes u)
  have parentLow : (J).arena.base (J).node + (J).arena.stride ≤ (J).scratch.hist :=
    (regions).node_before (node ▸ parentNodeFit)
  have hist : (J).scratch.hist ≤ upper := (Nat.le_add_right ..).trans
    (ShrinkCallCapacity.histogram_before regions (Fintype.card LeafStartup.ScalarPort) n)
  have halves (u z) : (reader).halfBits u z = packed X u z := (packed_eq_encode X u z).symm
  have names : ptr = (J).nodes := funext nodes
  have packetEq : packets = (reader).childPackets (J).nodes v old := by
    change xs.map (Child.packet X older B.recordLimit) = _
    rw [← encodedOld, ← names]
    simp only [children, List.map_ofFn, Function.comp_def, TermParsers.childPackets, Child.packet,
      Child.payload_ofHalf, halves]
    rfl
  have nd : (((reader).childPackets (J).nodes v old).map Packet.node).Nodup := by
    rw [TermParsers.childPackets_nodes (reader) (J).nodes v old, ← names]
    exact List.nodup_ofFn_ofInjective ((child_injective B i X older).comp
      (Subtype.val_injective.comp ((reader).order.children v).entries.injective))
  have degree : 2 ^ a i ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps + 1) ↦ 2 ^ S.degreeExponent j)
      (Finset.mem_univ i.castSucc)).trans (le_max_right ..)
  have hiddenFit : upper ≤ 2 ^ w := (Nat.le_add_right ..).trans room
  have fit : ∀ p ∈ packets, p.Fits (J).arena w n := by
    intro p member
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
    have length : (x.payload X).length ≤ (J).arena.stride := by
      rw [Child.payload_eq_packed]
      exact (packed_length_le X x.site (x.half X)).trans
        ((Nat.mul_le_mul (Nat.mul_le_mul_left 2 degree) wire).trans (Nat.le_succ _))
    exact ⟨Nat.le_add_right .., length, (Nat.add_le_add_left length _).trans
      (((regions).node_before (oldNodes x.site)).trans (hist.trans hiddenFit))⟩
  let childMem := storePackets (regions).arguments packets priv
  have written : scratch n childMem = writePackets (J).arena packets (scratch n priv) :=
    scratch_storePackets (J).arena packets priv
  have child := ShrinkPartyNative.Job.childWords_of_packets B f hf i X sel v old q J (reader)
    rfl halves (scratch n priv) childMem (packetEq ▸ fit) nd (packetEq ▸ written)
  have pe := parent_eq B i X sel workspace positions blocks cur sp n rowEnd older later
    v old parent q
  have distinct : ∀ p ∈ packets, p.node ≠ (J).node := by
    intro p member
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
    exact node ▸ (earlier x.site).ne
  have low : (J).arena.base (J).node + (packed Y _ (J).parent).length ≤ upper :=
    (Nat.add_le_add_left space.parentFit.2.1 _).trans (parentLow.trans hist)
  have field := (J).firstMapFields v hidden q childMem child
    (fun u ↦ (kidsLow u).trans hist) size room
  have parentKept := (J).parentStored_after_fields v hidden q childMem
    (Packet.mk (J).node (packed Y _ (J).parent)) (scratch n priv) packets fit distinct written
    space.parentFit (pe ▸ present) low size room
  exact ⟨space.packets _ field.1 parentKept, field.1, field.2, kidsLow, parentLow⟩

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
