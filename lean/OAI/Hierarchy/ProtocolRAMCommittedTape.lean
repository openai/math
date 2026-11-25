import OAI.Hierarchy.ProtocolRAMStockPortPlan
import OAI.Hierarchy.ProtocolRAMSelectedRows
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice

namespace OAI
/-! # The failed-row tape formed by an actual chronological native stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open AdaptiveProbe AdaptiveProbe.OuterBank RepairHistogram
open scoped BigOperators Fin.CommRing Classical
noncomputable section

variable {w q d rows paths : ℕ}

structure BroadcastRoom (s : StockCommit) (b : Batch q d) (rows w : ℕ) : Prop where
  fits : (broadcastTerm b s.price).Fits w s.direct
  keeps : ∀ j : Fin rows, commit_keeps s.plan s.occurrences s.goods (s.broadcast+j.val)

def tape (s : StockCommit) (b : Batch q d) (m : Memory w) (P : PortPlan s b m rows)
    (mount : (s.native w rows b).ready m) (bc : BroadcastRoom s b rows w)
    (keys : CashKeys s.occurrences rows s.goods paths)
    (link : Fin s.occurrences→ℕ→ℝ) (tree : Fin rows→ℕ→ℝ) :
    SelectedRows.Tape rows s.occurrences (Fin s.goods) where
  selected := liveRows b m rows
  ports := fun _=>d
  enum := P.enum
  kind := RepairHistogram.kind s.plan.bank s.columns m
  put := installedBits s.columns m
  take := consumedBits s.columns m
  weight := fun e=> link e (((s.native w rows b).after m) (keys.link e)).val
  broadcast := fun j=> let out := (s.native w rows b).after m
    (b.copies:ℝ)*(tree j (out (keys.broadcast j)).val*(out (s.broadcast+j.val)).val)
  dead := P.off
  quiet := by
    intro j absent
    have no : ¬committed b m (j.val:Word w) := by simpa [liveRows] using absent
    dsimp only
    rw [s.read_broadcast b m j mount bc.fits P.termRoom P.copyRoom P.sumRoom (bc.keeps j),ite_eq_right no]
    simp

structure StockRoom (s : StockCommit) (w payload cap : ℕ) : Prop where
  address : s.columns.destination.Fits w s.direct
  credit : s.columns.credit.Fits w s.direct
  debit : s.columns.charge.Fits w s.direct
  seed : s.plan.bank.base+s.goods≤ s.direct
  space : s.plan.bank.base+s.goods≤ s.plan.src
  wide : 4≤2^w
  limit : s.plan.limit=cap*payload
  room : s.plan.limit<2^w
  excess : s.plan.excess.base=s.plan.clip.base+s.goods
  clipCap : s.goods≤ s.plan.clip.size
  excessCap : s.goods≤ s.plan.excess.size
  bankCap : s.goods≤ s.plan.bank.size

/-- Width and quote are indexed by native row identity, including its actual
chosen packet. Inactive record widths and broadcasts have already been proved zero. -/
def failedRows {X : Type*} (s : StockCommit) (b : Batch q d) (m : Memory w) (P : PortPlan s b m rows)
    (mount : (s.native w rows b).ready m) (bc : BroadcastRoom s b rows w) (board : EventBoard s w)
    (keys : CashKeys s.occurrences rows s.goods paths) (link : Fin s.occurrences→ℕ→ℝ)
    (tree : Fin rows→ℕ→ℝ) (core : Fin s.goods→ℕ→ℝ) (fee : Fin paths→ℕ→ℝ)
    (flags sites payload K cap : ℕ) (ρ γ time : ℝ) (B : OuterBank (Fin s.goods) X) (x y : X)
    (width : Fin rows→ℕ) (positive : 0<payload) (room : StockRoom s w payload cap)
    (source : ∀ i : Fin s.goods, B.stock x i=(m (s.plan.bank.base+i.val)).val)
    (target : ∀ i : Fin s.goods, B.stock y i=(((s.native w rows b).after m) (s.plan.activeOut+i.val)).val)
    (funded : ∀ i : Fin s.goods, resourceBits (RepairHistogram.kind s.plan.bank s.columns m) (consumedBits (n:=s.occurrences) s.columns m) i≤
      (m (s.plan.bank.base+i.val)).val)
    (fit : ∀ i : Fin s.goods, (m (s.plan.bank.base+i.val)).val+
      resourceBits (RepairHistogram.kind s.plan.bank s.columns m) (installedBits (n:=s.occurrences) s.columns m) i<2^w)
    (mode : ∀ i : Fin s.goods, (s.plan.mode.eval (beforeTransfer s.columns s.plan s.occurrences s.goods
      (s.beforeApply b rows m)) (i.val:Word w)).val=2)
    (posting : B.cash y=B.cash x+∑ e,(s.eventWords flags payload b.copies keys link tree core fee e).value payload
      ((s.native w rows b).after m))
    (safeRoute : ∀ i,core i (((s.native w rows b).after m) (keys.core i)).val≤B.box i)
    (disabled : ∀ j : Fin paths, ((s.native w rows b).after m) (flags+j.val)=0)
    (many : ρ*sites≤(liveRows b m rows).card) (pos : ∀j∈liveRows b m rows,0<width j)
    (size : ∀j∈liveRows b m rows,2*(K*width j)≤payload)
    (quote : let T := s.tape b m P mount bc keys link tree
             let p := activePrice T.kind T.weight (maximizer B.a B.M time B.coefficient B.box (B.units payload x))
             ∀j∈liveRows b m rows, (∑ e, (T.put (P.enum ⟨j,e⟩):ℝ)*p (P.enum ⟨j,e⟩))+T.broadcast j+
               (AdaptiveProbe.copied K (width j) payload:ℝ)*(width j*γ/2)≤∑ e,(T.take (P.enum ⟨j,e⟩):ℝ)*p (P.enum ⟨j,e⟩))
    (curve : let T := s.tape b m P mount bc keys link tree
             (∑ i,(stockChange T.kind (netUnits payload T.put T.take) i)^2/(4*time*B.a))≤(sites:ℝ)*ρ*γ/(8*K)) :
    B.FailedRows sites payload K cap ρ γ time x y := by
  let raw : Fin s.goods → ℕ := RepairHistogram.raw s.plan.bank s.columns s.plan.src s.occurrences (s.beforeApply b rows m)
  have receipt (i : Fin s.goods) := s.repair_receipt b m i mount (by have := board.order; omega)
    room.address room.credit room.debit room.seed room.space room.wide payload cap room.limit room.room room.excess
    room.clipCap room.excessCap room.bankCap (funded i) (fit i) (mode i)
  apply (s.tape b m P mount bc keys link tree).failedRows B x y sites payload K cap ρ γ time raw width
  · intro i
    rw [source i]
    exact (receipt i).1
  · intro i
    rw [target i]
    exact (receipt i).2.1
  · rw [posting]
    exact s.failed_price b m flags payload b.copies cap positive mount board keys link tree core fee
      B.box (B.cash x) safeRoute (fun i=>(receipt i).2.2) disabled
  · exact many
  · exact pos
  · exact size
  · exact quote
  · exact curve

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
