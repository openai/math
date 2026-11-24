import OAI.Computability.VPVNP.PairShrinkRoleCanonicalData
import OAI.Computability.VPVNP.PairTreeDecoder

/-! # Private argument bounds for the children of a canonical shrinking row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords ShrinkBlockInputs LocalHistory
open NetworkKernel
open NodeArguments NodeArguments.ChildScan

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g w n p r : ℕ} {Z : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B Z} {v : MapResidentRows.Site Z}
  {site : CanonicalSite B i Z sel v w n (Fintype.card B.Entry)} {M : Machine w p r 11}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
  {lanes T : ℕ} {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
  {z : (B.execute f hf T hT X).Choices} {j : Fin (executeLevels B f hf T hT X z).length}
  {id : Fin (executeLevels B f hf T hT X z)[j].outputSites} {base : ℕ}

local notation "Y" => Z.shrinkNext B.shrink (S.shrink i) sel
local notation "addr" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (Y) v
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "ptr" => childNode Z site.older B.recordLimit
set_option quotPrecheck false in
local notation "rdr" => (shrinkPassReaders B f hf i rfl Z).termParsers sel

/-- The tree reader enumerates the descriptor's children in their physical order. Each of
their half-wire packets fits the reserved argument slot above the geometry pointer. The
histogram starts strictly beyond that pointer even for an empty child list. -/
theorem CanonicalSiteData.childPacketFits (data : CanonicalSiteData site M f hf T hT X z j id base)
    (node : Word w) (atRow : node.val = addr)
    (old : Placed ((B.shrinkPassAt f hf i rfl Z).step.term sel).place Z.network.Half v) :
    let packets := TreeDecode.children rdr (fun u b => Packet.mk (ptr u) (packed Z u b)) v old
    (∀ q ∈ packets, q.Fits (regions).arguments w n) ∧
      (∀ q ∈ packets, q.node < (regions).nodes) ∧
      (∀ q ∈ packets, n < (regions).arguments.base q.node) ∧ n < (regions).histBase := by
  let order := (rdr).order.children v
  have row := (data.directory node atRow).2
  have packetBounds (k : Fin order.length) :
      let u := order.entries k
      let q := Packet.mk (ptr u.val) (packed Z u.val (old u.val u.prop))
      q.Fits (regions).arguments w n ∧
        q.node < (regions).nodes ∧ n < (regions).arguments.base q.node := by
    let u := order.entries k
    have member : u.val ∈ (site.descriptor node).sites := by
      rw [data.orderAt node atRow]
      exact List.mem_ofFn.mpr ⟨k, rfl⟩
    have size : (packed Z u.val (old u.val u.prop)).length = ChildArguments.width Z u.val := by
      rw [← Child.payload_ofHalf]
      exact Child.payload_length Z _
    exact ⟨⟨row.stack _ member, size ▸ row.stride _ member, size ▸ (row.room _ member).le⟩,
      data.oldNodes _, data.abovePointer _⟩
  have all q (hq : q ∈ TreeDecode.children rdr (fun u b => Packet.mk (ptr u) (packed Z u b))
      v old) : q.Fits (regions).arguments w n ∧ q.node < (regions).nodes ∧
        n < (regions).arguments.base q.node := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
    exact packetBounds k
  have positive : 0 < site.rowEnd := Nat.zero_lt_of_lt data.parentFit
  have before : n < (regions).histBase := by
    change n < n + site.rowEnd * (2 * slotDegree S * n + 1)
    exact Nat.lt_add_of_pos_right (Nat.mul_pos positive (Nat.succ_pos _))
  exact ⟨fun q hq => (all q hq).1, fun q hq => (all q hq).2.1,
    fun q hq => (all q hq).2.2, before⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
