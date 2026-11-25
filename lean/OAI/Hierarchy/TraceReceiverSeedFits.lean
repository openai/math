import OAI.Hierarchy.TraceReceiverSeedInstalled
import OAI.Hierarchy.TraceReceiverKeyAll

namespace OAI
/-! # Every sufficiently large physical receiver admits the genuine selected leaf ROM -/

namespace Hierarchy.TraceReceiverSeedInstalled
open Filter ThreeFlat Diagonal TraceBitHeader RAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (F : Type) [Fintype F] [Field F]

/-- For the agreed 26J compact gate template, the key, table, dictionary,
virtual array, field and operand-width prices all hold at the same physical word width. -/
theorem eventually_fits (copies : ℕ) : ∀ᶠ w : ℕ in atTop, ∀ {pc regs slots S base q low fuel : ℕ}
    (M : Machine (64*w) pc regs slots) (t : NativeTrace.Fits M S base ((q+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w)), pc≤64*w → regs≤64*w → slots≤64*w →
    (q+1)+low≤2*w+1 →
    let J := 2^(32*w)
    HistorySelectedSeedDecode.Fits (q:=q) (low:=low) (S:=S) (f:=fuel) (b:=4*w+2) (W:=64*w)
      hF t.width t.labels base st t.header t.time regs slots copies 0 (27*J) (27*J+2^((q+1)+low)) (26*J) := by
  filter_upwards [TraceReceiverKeyBounds.eventually_literal,TraceReceiverLeafRoom.eventual_margin F copies,
    eventual_count,eventually_ge_atTop (Fintype.card F),eventually_ge_atTop (Fintype.card ((Fin 3→Bool)→F)),
    eventually_ge_atTop 7] with w key budget table smallField smallLibrary hw
  intro pc regs slots S base q low fuel M t hF st hp hr hk hd
  let d := (q+1)+low
  let J := 2^(32*w)
  let G := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs slots d
  let masks := 27*J+2^d
  let tmp := masks+TraceReceiverMaskBanks.count (q+1) low
  have depth : d≤64*w := by dsimp [d];omega
  have count := (TraceReceiverTemplate.count_bound M t hF st (by omega) hp hr hk depth).trans table
  obtain ⟨rawStop,lower,_,_,space⟩ := storage M t hF st hw hd count
  have price := TraceReceiverLeafRoom.footprint F M t hF st copies 0 (27*J) masks (26*J+FixedTraceImage.count G)
    (by omega) hp hr hk depth
  obtain ⟨fitsBudget,word⟩ := budget d hd
  have library : Fintype.card ((Fin 3→Bool)→F)≤2^(64*w) := by
    have cap := Nat.lt_two_pow_self (n:=64*w)
    omega
  exact fits M t hF st copies 0 (26*J) (27*J) masks tmp
    (by simpa only [Nat.zero_add] using rawStop) lower le_rfl le_rfl space
    (key M t (by omega) hp hr hk) (price.trans_lt fitsBudget) word (by omega) library

end
end Hierarchy.TraceReceiverSeedInstalled

end OAI
