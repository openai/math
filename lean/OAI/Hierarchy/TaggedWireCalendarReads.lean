import OAI.Hierarchy.TaggedWireReadBanks
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMRepairHistogram

namespace OAI
/-! # Causal execution across frozen purchases, sparse stock commits, and calendar boundaries -/

namespace Hierarchy.WireTelescope.ReadBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProtocolRAM ProtocolRAM.Calendar PhysicalProcedure
open scoped Fin.CommRing
variable {W q d : ℕ}

theorem repair_result (bank : RepairHistogram.Columns) (src n : ℕ)
    {future : ℕ→Prop} {m m' : Memory W} (same : Agree future m m')
    (table : NoFuture future (RepairHistogram.pair bank)) (dest : NoFuture future bank.destination)
    (credit : NoFuture future bank.credit) (debit : NoFuture future bank.charge) :
    Agree future (RepairHistogram.result bank src n m) (RepairHistogram.result bank src n m') := by
  have addr : RepairHistogram.address (n:=n) bank m=RepairHistogram.address bank m' := by
    funext i
    exact congrArg Fin.val (eval bank.destination same dest _)
  have delta : RepairHistogram.delta (n:=n) bank m=RepairHistogram.delta bank m' := by
    funext i
    simp only [RepairHistogram.delta,eval bank.credit same credit,eval bank.charge same debit]
  intro a outside
  simp only [RepairHistogram.result,ProtocolRAMWeightedScatter.image,addr,delta]
  rw [scan src (2*n) _ same table a outside]

/-- At old public stock and physical link cells below the paired scratch
area, only the actual occurrence addresses and signed credit/debit values
can affect the next word. -/
theorem repair_observed (p : RepairHistogram.Columns) (src n : ℕ)
    (m m' : Memory W) (live : ℕ→Prop) (same : ∀a,live a→m a=m' a)
    (read : ∀i : Fin n,Observed live m (i.val:Word W) p.destination ∧
      Observed live m (i.val:Word W) p.credit ∧ Observed live m (i.val:Word W) p.charge)
    (a : ℕ) (past : a<src) (stock : live a) :
    RepairHistogram.result p src n m a=RepairHistogram.result p src n m' a := by
  have addr : RepairHistogram.address (n:=n) p m=RepairHistogram.address p m' := by
    funext i
    exact congrArg Fin.val (eval_observed live m m' same _ _ (read i).1)
  have delta : RepairHistogram.delta (n:=n) p m=RepairHistogram.delta p m' := by
    funext i
    simp only [RepairHistogram.delta,eval_observed live m m' same _ _ (read i).2.1,
      eval_observed live m m' same _ _ (read i).2.2]
  simp only [RepairHistogram.result,ProtocolRAMWeightedScatter.image,addr,delta,
    ProtocolRAM.image,fillSegment,not_le.mpr past,false_and,ite_false,same a stock]

theorem fed (C : Chart W q d) (b : Boundary) {future : ℕ→Prop} {m m' : Memory W}
    (same : Agree future m m') (safe : ∀ p∈feedPasses C b,NoFuture future p.term) :
    Agree future (after C (.feed b) m) (after C (.feed b) m') :=
  passes (feedPasses C b) same safe

/-- Instructions in the actual trace establish independence even for the
frozen block's indirect address computations. A second run on another
future certificate ends with the same observed state on every current cell. -/
theorem step_causal (C : Chart W q d) (e : Event) {future : ℕ→Prop} {m m' : Memory W}
    (same : Agree future m m') (valid : ready C e m) (valid' : ready C e m')
    (safe : ProcedureReads future (step C e) (ticks C e) m) :
    Agree future (after C e m) (after C e m') :=
  executed _ _ same safe (step_exec C e m valid) (step_exec C e m' valid')

def PublicPrefix (C : Chart W q d) (future : ℕ→Prop) : List Event → Memory W → Prop
  | [],_=>True
  | e::es,m=>ProcedureReads future (step C e) (ticks C e) m ∧ PublicPrefix C future es (after C e m)

theorem prefix_causal (C : Chart W q d) (es : List Event) {future : ℕ→Prop} {m m' : Memory W}
    (same : Agree future m m') (left : mounted C es m) (right : mounted C es m')
    (safe : PublicPrefix C future es m) : Agree future (run C es m) (run C es m') := by
  induction es generalizing m m' with
  | nil => exact same
  | cons e es ih => exact ih (step_causal C e same left.1 right.1 safe.1) left.2 right.2 safe.2

theorem selected (b : Batch q d) {future : ℕ→Prop} {m m' : Memory W} (same : Agree future m m')
    (ctrl : PublicBank future b.enabled) (owner : NoFuture future b.owner)
    (packet : NoFuture future b.packet) (need : ∀i,NoFuture future (b.need i))
    (stock : ∀i,NoFuture future (b.stock i)) (r : Word W) : b.selected m r ↔ b.selected m' r := by
  simp only [Batch.selected,eval b.owner same owner,bank_read b.enabled same ctrl,eval b.packet same packet,
    fun i=>eval (b.need i) same (need i),fun i=>eval (b.stock i) same (stock i)]

theorem alphabet (b : Batch q d) {future : ℕ→Prop} {m m' : Memory W} (same : Agree future m m')
    (ctrl : PublicBank future b.termCount) (packet : NoFuture future b.packet) (r : Word W) :
    b.termCount.read m (b.packet.eval m r) = b.termCount.read m' (b.packet.eval m' r) := by
  rw [eval b.packet same packet,bank_read b.termCount same ctrl]

/-- Only the current candidate's enabled bit, packet, demands and stocks
affect its admission class, even when dead solver scratch shares the tape. -/
theorem selected_observed (b : Batch q d) (m m' : Memory W) (r : Word W) (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a) (enable : Observed live m r (.lookup b.enabled b.owner))
    (packet : Observed live m r b.packet) (demand : ∀i,Observed live m r (b.need i))
    (stock : ∀i,Observed live m r (b.stock i)) : b.selected m r ↔ b.selected m' r := by
  have gate := eval_observed live m m' same (.lookup b.enabled b.owner) r enable
  change b.enabled.read m (b.owner.eval m r) = b.enabled.read m' (b.owner.eval m' r) at gate
  simp only [Batch.selected,gate,eval_observed live m m' same b.packet r packet,
    fun i=>eval_observed live m m' same (b.need i) r (demand i),
    fun i=>eval_observed live m m' same (b.stock i) r (stock i)]

theorem alphabet_observed (b : Batch q d) (m m' : Memory W) (r : Word W) (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a) (read : Observed live m r (.lookup b.termCount b.packet)) :
    b.termCount.read m (b.packet.eval m r) = b.termCount.read m' (b.packet.eval m' r) :=
  eval_observed live m m' same _ r read

end Hierarchy.WireTelescope.ReadBanks

end OAI
