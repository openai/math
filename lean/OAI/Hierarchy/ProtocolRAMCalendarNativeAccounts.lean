import OAI.Hierarchy.ProtocolRAMCalendarEventPrices
import OAI.Hierarchy.ProtocolRAMCalendarStockAt
import OAI.Hierarchy.ProtocolRAMCalendarBootFrame
import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.ProbeCommodityBounds

namespace OAI
/-! # Concrete current inventory, cumulative financial charge and physical startup cost -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe OuterBank
open ThreeFlat.RAM (fillSegment)
open scoped BigOperators Classical
noncomputable section
variable {w z d k N q goods : ℕ}

def nativeAccounts (c : Mesh) (arena : Arena) (f : Attempt→Format z d k q goods) (initial payload : ℕ)
    (billed : Event→WordRows) (baseFee a M beta : ℝ) (cap : ℕ→ℝ) :
    AccountColumns (Commodity (Fin (2^z)) N k) :=
  (postedRows c billed).account c ⟨payload,stockAt c arena f initial,fun _=>0,fun _=>Fin.elim0,
    fun _=>Fin.elim0,fun _=>Fin.elim0,baseFee,payloadUnit,fun i=>cap (PurchaseInventory.lane i),
    bonus beta,a,M⟩

theorem nativeAccounts_initial (c : Mesh) (arena : Arena) (f : Attempt→Format z d k q goods) (initial payload : ℕ)
    (billed : Event→WordRows) (baseFee a M beta : ℝ) (cap : ℕ→ℝ) (m : Memory w) :
    let A := nativeAccounts (N:=N) c arena f initial payload billed baseFee a M beta cap
    (A.read (.outer 0 0) m).bits=(fun i=>(m (initial+PurchaseInventory.slot i)).val) ∧
      (A.read (.outer 0 0) m).paid=baseFee := by
  constructor
  · funext i
    change (m (stockAt c arena f initial (.outer 0 0) i)).val=_
    rw [stockAt_initial]
  · have first : cursor c (.outer 0 0)=0 := by simp [cursor,position,trialBase]
    let P := postedRows c billed
    let amount (j : ℕ) := ∑ r : Fin (P.size j),
      ((m (P.word j r).width).val : ℝ) * (P.word j r).price (m (P.word j r).key).val
    have empty : amount 0=0 := by
      change (∑ r : Fin 0, ((m (P.word 0 r).width).val : ℝ) *
        (P.word 0 r).price (m (P.word 0 r).key).val)=0
      simp
    change baseFee + amount (cursor c (.outer 0 0)) / (payload : ℝ) = baseFee
    rw [first,empty,zero_div,add_zero]

/-- The state at the completion of the reserve mesh is exactly the next outer
trial, both for the live stock coordinates and for the full signed word history. -/
theorem nativeAccounts_outer_next (C : Chart w q d) (arena : Arena) {zz dd kk qq goods : ℕ}
    (f : Attempt→Format zz dd kk qq goods) (initial payload : ℕ)
    (billed : Event→WordRows) (baseFee a M beta : ℝ) (cap : ℕ→ℝ) (m : Memory w) (p h : ℕ) :
    let A := nativeAccounts (N:=N) C.mesh arena f initial payload billed baseFee a M beta cap
    A.inner C m p h C.mesh.reserveSteps 0=A.trial C m p (h+1) := by
  dsimp only [AccountColumns.inner,AccountColumns.trial]
  rw [inner_zero,trial_succ]
  apply PriceHistory.alias
  · exact (position_trial_end C.mesh p h).symm
  · exact funext (stockAt_purchase_end C.mesh arena f initial p h)

/-- The initial live bank is a dense empty inventory independent of the permutation.
The startup procedure may fill its sampler tables and subdivision data around it. -/
def zeroInventory (z N k base : ℕ) (m : Memory w) : Memory w :=
  fillSegment base (PurchaseInventory.footprint z N k) (fun _=>0) m

theorem boot_zero_inventory {jobs : ℕ} (base : ℕ) (v : Fin jobs→Market z d k)
    (π : Equiv.Perm (Fin (2^z))) (raw mid : Boot.Tape z d)
    (start : Boot.Receipt v π (zeroInventory z N k base raw) mid)
    (low : heapEnd z d copies≤base) (high : ∀j,base+PurchaseInventory.footprint z N k≤Boot.low (v j))
    (i : Commodity (Fin (2^z)) N k) : mid (base+PurchaseInventory.slot i)=0 := by
  have fit := PurchaseInventory.slot_lt i
  have inside : base≤base+PurchaseInventory.slot i ∧ base+PurchaseInventory.slot i<base+PurchaseInventory.footprint z N k := by omega
  rw [start.kept _ (low.trans inside.1) (fun j mem=>(inside.2.trans_le (high j)).not_ge mem.1)]
  simp [zeroInventory,fillSegment,inside]

/-- The fixed price of the actual initialized sampler, fixed connections,
radius links, and paid core at this width and height. -/
def coreDebit (S : PurchaseSampler) (h d k : ℕ) (p q Q Λ t M : ℝ) :=
  ∑e : CoreBoard.Edges S h d k,Λ*capacity p q Q (coreScale t e) (coreLength (CoreBoard.freeLength M) e)

/-- The initial financial promise holds at zero inventory in the actually read
physical bank with the complete public fixed-edge invoice. -/
theorem eventually_initial (k : ℕ) {p σ Λ : ℝ} (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) :
    ∀ᶠ W : ℕ in Filter.atTop,∀ (z : ℕ) (S : PurchaseSampler) (M qq Q : ℝ) (c : Mesh)
      (arena : Arena) (f : Attempt→Format z (2^W) k q goods) (initial payload : ℕ)
      (billed : Event→WordRows) (a beta : ℝ) (cap : ℕ→ℝ) (m : Memory w),
      let A := nativeAccounts (N:=CoreBoard.Stages z (2^W)) c arena f initial payload billed
        (coreDebit S z (2^W) k p qq Q Λ (dyadicScale W) M) a M beta cap
      0≤a → 0≤beta → (∀i : Commodity (Fin (2^z)) (CoreBoard.Stages z (2^W)) k,
         m (initial+PurchaseInventory.slot i)=0) →
      A.bank.balance payload 1 (A.read (.outer 0 0) m)≤(2^z:ℕ) := by
  filter_upwards [CoreBoard.affordable k hp hσ hΛ] with W invoice
  intro z S M qq Q c arena f initial payload billed a beta cap m A ha hb empty
  have seeded := nativeAccounts_initial (N:=CoreBoard.Stages z (2^W)) c arena f initial payload billed
    (coreDebit S z (2^W) k p qq Q Λ (dyadicScale W) M) a M beta cap m
  apply A.bank.initial_balance
  · intro i
    change (A.read (.outer 0 0) m).bits i=0
    simpa only [empty,Fin.val_zero] using congrFun seeded.1 i
  · exact ha
  · intro i
    change 0≤bonus beta i
    cases i <;> simp [bonus,hb]
  · change (A.read (.outer 0 0) m).paid≤_
    rw [seeded.2]
    exact invoice z S M qq Q

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
