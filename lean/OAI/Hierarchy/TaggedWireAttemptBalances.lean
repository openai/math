import OAI.Hierarchy.TaggedWireFeedMatrix
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice

namespace OAI
/-! # Every attempt's actual clipped, bought or untouched commodity words -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open ProtocolRAM Calendar AdaptiveProbe WireTelescope Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {h d k W rows q t : ℕ} (s : StockCommit) (b : Batch q t) (m : Memory W)
    (fits : ∀i : Data h d k,PurchaseInventory.slot i<s.goods)

private def key (i : Data h d k) : Fin s.goods := ⟨PurchaseInventory.slot i,fits i⟩
local notation "u" => s.beforeApply b rows m
local notation "modeAt" => RepairHistogram.beforeTransfer s.columns s.plan s.occurrences s.goods u
local notation "final" => (s.native W rows b).after m
local notation "amount" => RepairHistogram.raw s.plan.bank s.columns s.plan.src s.occurrences u
local notation "available" => PurchaseInventory.stock s.plan.bank.base m
local notation "out" => PurchaseInventory.stock s.plan.activeOut final
local notation "saved" => PurchaseInventory.stock (s.plan.activeOut+s.goods) final
local notation "extra" => PurchaseInventory.stock (s.plan.activeOut+s.goods+s.goods) final

/-- For a repair, only the post-histogram amount is recoded by the cap.
Each unit of overflow belongs to its original directed commodity. -/
def repaired (cap payload : ℕ) (ready : (s.native W rows b).ready m) (order : s.direct≤ s.broadcast)
    (address : s.columns.destination.Fits W s.direct) (credit : s.columns.credit.Fits W s.direct)
    (debit : s.columns.charge.Fits W s.direct) (seed : s.plan.bank.base+s.goods≤ s.direct)
    (space : s.plan.bank.base+s.goods≤ s.plan.src) (wide : 4≤2^W) (limit : s.plan.limit=cap*payload)
    (room : s.plan.limit<2^W) (excess : s.plan.excess.base=s.plan.clip.base+s.goods)
    (clipCap : s.goods≤ s.plan.clip.size) (excessCap : s.goods≤ s.plan.excess.size) (bankCap : s.goods≤ s.plan.bank.size)
    (funded : ∀ i : Fin s.goods,OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m)
      (RepairHistogram.consumedBits (n:=s.occurrences) s.columns m) i≤(m (s.plan.bank.base+i.val)).val)
    (fit : ∀ i : Fin s.goods,(m (s.plan.bank.base+i.val)).val+OuterBank.resourceBits (RepairHistogram.kind s.plan.bank s.columns m)
      (RepairHistogram.installedBits (n:=s.occurrences) s.columns m) i<2^W)
    (mode : ∀i : Data h d k,(s.plan.mode.eval modeAt (PurchaseInventory.slot i:Word W)).val=2) :
    Transfer h d k where
  old _:=0
  active i:=amount (key s fits i)
  held _:=0
  kept:=out
  spill:=extra
  balanced i:=by
    let a:=key s fits i
    obtain ⟨_,clipped,overflow⟩:=s.repair_receipt (rows:=rows) b m a ready order address credit debit seed space wide payload cap
      limit room excess clipCap excessCap bankCap (funded a) (fit a) (mode i)
    change 0+amount a=0+(final (s.plan.activeOut+a.val)).val+(final (s.plan.activeOut+s.goods+s.goods+a.val)).val
    rw [clipped,overflow]
    simp only [spillBits,clipBits]
    omega

/-- Buying transfers exactly the undelivered complement to the saved bank,
including the high unit for an odd-width purchase. -/
def bought (ready : (s.native W rows b).ready m) (order : s.direct≤ s.broadcast)
    (credit : s.columns.credit.Fits W s.direct) (debit : s.columns.charge.Fits W s.direct)
    (before : s.plan.bank.base+s.goods≤ s.direct) (space : s.plan.bank.base+s.goods≤ s.plan.src)
    (fresh : s.plan.bank.base+s.goods≤ s.plan.clip.base) (wide : 4≤2^W) (cap : s.goods≤ s.plan.bank.size)
    (idle : ∀e : Fin s.occurrences,RepairHistogram.delta s.columns m e=0)
    (mode : ∀ i : Data h d k,(s.plan.mode.eval modeAt (PurchaseInventory.slot i:Word W)).val=3)
    (half : ∀ i : Data h d k,let x:=s.plan.bank.read modeAt (PurchaseInventory.slot i:Word W)
      (s.plan.half.read modeAt x).val=x.val/2) : Transfer h d k where
  old _:=0
  active:=available
  held:=saved
  kept:=out
  spill:=extra
  balanced i:=by
    let a:=key s fits i
    obtain ⟨active,held,overflow⟩:=s.buy_receipt (rows:=rows) b m a ready order credit debit before space fresh wide cap idle
      (mode i) (half i)
    change 0+(m (s.plan.bank.base+a.val)).val=(final (s.plan.activeOut+s.goods+a.val)).val+
      (final (s.plan.activeOut+a.val)).val+(final (s.plan.activeOut+s.goods+s.goods+a.val)).val
    rw [held,active,overflow]
    simp only [Fin.val_zero]
    omega

/-- A skipped attempt preserves the actual undelivered portion of an older
purchase, even after some of its archived original reserve has been fed. -/
def copied (delivered : Data h d k→ℕ) (ready : (s.native W rows b).ready m) (order : s.direct≤ s.broadcast)
    (credit : s.columns.credit.Fits W s.direct) (debit : s.columns.charge.Fits W s.direct)
    (before : s.plan.bank.base+s.goods≤ s.direct ∧ s.plan.reserve.base+s.goods≤ s.direct)
    (space : s.plan.bank.base+s.goods≤ s.plan.src ∧ s.plan.reserve.base+s.goods≤ s.plan.src)
    (fresh : s.plan.bank.base+s.goods≤ s.plan.clip.base ∧ s.plan.reserve.base+s.goods≤ s.plan.clip.base)
    (wide : 4≤2^W) (cap : s.goods≤ s.plan.bank.size ∧ s.goods≤ s.plan.reserve.size)
    (apart : s.plan.bank.base+s.goods<s.plan.reserve.base ∨ s.plan.reserve.base+s.goods≤ s.plan.bank.base)
    (idle : ∀ e : Fin s.occurrences,RepairHistogram.delta s.columns m e=0)
    (mode : ∀ i : Data h d k,(s.plan.mode.eval modeAt (PurchaseInventory.slot i:Word W)).val≠2 ∧
      (s.plan.mode.eval modeAt (PurchaseInventory.slot i:Word W)).val≠3) : Transfer h d k where
  old i:=PurchaseInventory.stock s.plan.reserve.base m i-delivered i
  active:=available
  held i:=saved i-delivered i
  kept:=out
  spill:=extra
  balanced i:=by
    let a:=key s fits i
    obtain ⟨active,held,overflow⟩:=s.copy_receipt (rows:=rows) b m a ready order credit debit before space fresh wide cap apart idle (mode i)
    change (m (s.plan.reserve.base+a.val)).val-delivered i+(m (s.plan.bank.base+a.val)).val=
      (final (s.plan.activeOut+s.goods+a.val)).val-delivered i+(final (s.plan.activeOut+a.val)).val+
        (final (s.plan.activeOut+s.goods+s.goods+a.val)).val
    rw [held,active,overflow]
    simp

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer

end
end OAI
