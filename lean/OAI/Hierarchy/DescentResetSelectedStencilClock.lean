import OAI.Hierarchy.DescentResetChosenStencilVolume
import OAI.Hierarchy.DescentResetSelectedAtlasTraffic
import OAI.Hierarchy.DescentPhysicalResetStencilTariff
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! The scheduled stencil may use a smaller receiver batch than its stand-alone
Walsh endpoint chart. Every measured occurrence uses the selected batch here. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentDatedAddressBook DescentSIMDLookup DescentPackedWalsh DescentFallbackPeriod
open ProtocolRAM DescentStaticWordColumn
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d k i D n C f g rate tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist) (rates : ResetRates G S k D n h₀ C f g rate tail)
    (p h drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "c₀" => S.groupWidth k tail i
local notation "bits₀" => S.localWalshBits p (c₀+k) f (quota S.rounds)
local notation "cut₀" => resetCut S k tail p f h i
local notation "rawCap" => (((capCalendar G.b S.rounds g S.height).take i).prod*256)
local notation "date₀" => PhysicalReset.selected G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old io.wire io.roster floor
local notation "e₀" => PhysicalReset.receiverCut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old
local notation "mid₀" => (date₀).successor.middle
local notation "bound₀" => PhysicalReset.selected_cut G S rates.board k tail i p f g drift degree h
  cut₀ nextM C packet oldLanes primitiveLanes printedBits old

local notation "v" => (date₀).successor
local notation "at₀" => (date₀).rebased ((date₀).stageStart floor)
local notation "base₀" => (v).actorEnd at₀
local notation "cal" => capCalendar G.b S.rounds g S.height

local notation "shape₀" => selected_stencil_shape (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
local notation "txn" count:arg => (date₀).stencilPhase shape₀ ((date₀).stageStart floor) count io.hubs g (2^n)
local notation "dim" => c₀+k
local notation "low" => laneBits dim h bits₀
local notation "A" => stencilCapacity k bits₀ old.degree n
open DescentPlainTerminal.Suffix PackedFlow.Padded ThreeFlat.Routing

private theorem positive_chunks (c e : ℕ) : 0 < chunks (2^c) (2^e) := by
  have room := CallPool.count_le_batches_mul (2^c) (2^e) (Nat.two_pow_pos _)
  change 2^c ≤ 2^e * chunks (2^c) (2^e) at room
  by_contra! zero
  rw [Nat.eq_zero_of_le_zero zero, Nat.mul_zero] at room
  exact (Nat.two_pow_pos _).not_ge room

theorem selected_stencil_clock (count : Bank) (w : ℕ) (oldHosts : 0<S.hostSize i)
    (lowFits : k≤low) (word : 8*bits₀≤h) (rootRoom : 8*(v).groupWidth≤h)
    (range : Nat.clog 2 (dim+2)+(dim+S.censusBits p)≤h/2) :
    let R:=(txn count)
    (R.time w+7*names (R.code w))*w ≤
      remixInvoice (S.endpointBook k tail i p f old.degree h n) R.chart R.origin R.solve R.fresh R.counts R.peers h w R.positive+
      (1200000*(A+1)^3*(S.hostSize i+S.hostSize i*chunks (2^c₀) (2^e₀)+(h+1)^3*2^(h/2)))*w := by
  let R:=(txn count)
  let st:=R.S
  have depth : st.r=k:=by change c₀+k-c₀=k; exact Nat.add_sub_cancel_left ..
  have inside : e₀+st.r≤laneBits st.m h st.b:=by
    rw [depth]
    change e₀+k≤low
    exact (Nat.add_le_add_right (bound₀).2.1 k).trans_eq (Nat.sub_add_cancel lowFits)
  have rate : R.ratio=2^(laneBits st.m h st.b-st.r-e₀):=by rw [depth];rfl
  have paid : sharedWidth st*st.M≤h/2 := by
    have member : sharedWidth st ∈ (v).rootUnits := List.Mem.head _
    have fit := (v).operand_room cut₀ cut₀ (S.groupWidth k tail (i+1)) h rootRoom (Or.inl member)
    have selected := selected_root_exponent (i:=i) rates p h drift degree nextM packet oldLanes
      primitiveLanes printedBits old io.wire io.roster floor
    rw [selected] at fit
    exact fit
  have positive := positive_chunks c₀ e₀
  have rows:0< st.rows:=Nat.mul_pos oldHosts positive
  have size:dim≤bits₀:=by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  have small:k≤2^k:=Nat.lt_two_pow_self.le
  have bought:2^st.r≤A:=by rw [depth];unfold stencilCapacity;omega
  have padding:8*(bits₀+old.degree+n+7)≤A:=by unfold stencilCapacity;omega
  have axes:st.m≤A:=by change dim≤A;omega
  have degreeFit:st.degree≤A:=by change old.degree≤A;omega
  have bits:st.b≤A:=by change bits₀≤A;omega
  have newWidth:st.n≤A:=by change k+bits₀+2≤A;unfold stencilCapacity;omega
  have targets:st.t≤A:=by change 2*k+n+2≤A;omega
  have scalar:R.X.count.work≤A:=by change 6≤A;omega
  exact R.chosen_clock e₀ h w A rfl rfl rfl rate word inside rows paid range bought axes degreeFit bits
    newWidth targets scalar degreeFit

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
