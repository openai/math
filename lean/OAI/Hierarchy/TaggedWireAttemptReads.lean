import OAI.Hierarchy.TaggedWireMarketReads

namespace OAI
/-! # The three actual price tests and the fixed-packet admission mask -/

noncomputable section
namespace Hierarchy.WireTelescope.ReadBanks
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAM.AttemptGate ProtocolRAM.PurchaseStage
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {W q d : ℕ}

def Written (old : ℕ→Prop) (base count a : ℕ) := (base≤a ∧ a<base+count) ∨ old a

def CheckLive (old : ℕ→Prop) (check : Check) := Written old check.out (check.rows+1)

theorem check_words (c : Check) {m m' : Memory W} (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a)
    (reads : ∀i : Fin c.rows,Observed live m (i.val:Word W) c.term) :
    ∀a,CheckLive live c a→c.after m a=c.after m' a := by
  have values : c.score m = c.score m' := by
    funext i
    exact congrArg Fin.val (eval_observed live m m' same c.term _ (reads i))
  intro a valid
  change (if c.out≤a ∧ a<c.out+(c.rows+1) then _ else _) =
    (if c.out≤a ∧ a<c.out+(c.rows+1) then _ else _)
  by_cases inside : c.out≤a ∧ a<c.out+(c.rows+1)
  · simp only [ite_eq_left inside,values]
  · exact (ite_eq_right inside).trans ((same a (valid.resolve_left inside)).trans (ite_eq_right inside).symm)

theorem scan_words (out n : ℕ) (e : Expr) {m m' : Memory W} (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a)
    (reads : ∀i : Fin n,Observed live m (i.val:Word W) e) :
    ∀a,Written live out n a→image out n e m a=image out n e m' a := by
  intro a valid
  apply pass_word ⟨out,n,e⟩ live m m' same a
  by_cases inside : out≤a ∧ a<out+n
  · rw [ite_eq_left inside]
    let i : Fin n := ⟨a-out,by omega⟩
    have eqn : ((a:Word W)-(out:Word W))=(i.val:Word W) := by
      have h : a=out+i.val := (Nat.add_sub_of_le inside.1).symm
      calc
        _ = ((out+i.val:ℕ):Word W)-(out:Word W) := congrArg (fun v : ℕ=>(v:Word W)-(out:Word W)) h
        _ = _ := by rw [Nat.cast_add]; abel
    rw [eqn]
    exact reads i
  · rw [ite_eq_right inside]
    exact valid.resolve_left inside

def SnapshotLive (live : ℕ→Prop) (z : Dispatch) (B : Repair q d) :=
  Written (CheckLive (CheckLive (CheckLive live B.tests.excess) B.tests.payload) B.tests.discrepancy)
    B.repairBits.base z.candidates

/-- Compute the true post-purchase snapshot without ever inspecting a future
histogram field. The successive live sets retain the earlier tests' outputs. -/
theorem snapshot_words (L : Dispatch) (B : Repair q d) {m m' : Memory W} (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a)
    (excess : ∀i : Fin B.tests.excess.rows,Observed live m (i.val:Word W) B.tests.excess.term)
    (payload : ∀i : Fin B.tests.payload.rows,Observed (CheckLive live B.tests.excess)
      (B.tests.excess.after m) (i.val:Word W) B.tests.payload.term)
    (disp : ∀i : Fin B.tests.discrepancy.rows,Observed (CheckLive (CheckLive live B.tests.excess) B.tests.payload)
      (B.tests.payload.after (B.tests.excess.after m)) (i.val:Word W) B.tests.discrepancy.term)
    (repair : ∀i : Fin L.candidates,Observed (CheckLive (CheckLive (CheckLive live B.tests.excess) B.tests.payload) B.tests.discrepancy)
      (B.tests.after m) (i.val:Word W) (repairMask B)) :
    ∀a,SnapshotLive live L B a→postSnapshot L B m a=postSnapshot L B m' a := by
  have x := check_words B.tests.excess live same excess
  have y := check_words B.tests.payload _ x payload
  have z := check_words B.tests.discrepancy _ y disp
  exact scan_words B.repairBits.base L.candidates (repairMask B) _ z repair

def OutputLive (L : Dispatch) (B : Repair q d) (live : ℕ→Prop) (a : ℕ) : Prop :=
  (live a ∧ a<B.verdict ∧ ∀u∈audits L B,a<u.low) ∨
    ∃p∈writes L B,∃j : Fin p.rows,a=p.out+j.val

/-- Every actual emitted stock, price, selector and descriptor column depends
only on its row expression at the precommit snapshot. The admission scan's
temporary work cells are never requested by this output projection. -/
theorem output_words (L : Dispatch) (B : Repair q d) (m m' : Memory W) (live : ℕ→Prop)
    (ready : AuditReady (audits L B) (postSnapshot L B m))
    (ready' : AuditReady (audits L B) (postSnapshot L B m')) (board : Board L B W)
    (same : ∀a,live a→postSnapshot L B m a=postSnapshot L B m' a)
    (reads : ∀p∈writes L B,∀ j : Fin p.rows,Observed live (postSnapshot L B m) (j.val:Word W) p.term) :
    ∀a,OutputLive L B live a→postOutput L B m a=postOutput L B m' a := by
  rintro a (⟨active,low,safe⟩|⟨p,hit,j,rfl⟩)
  · have below (v : Memory W) (pending : AuditReady (audits L B) (postSnapshot L B v)) :
        postOutput L B v a=postSnapshot L B v a :=
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl low)).trans
        (audit_below _ _ pending a safe)
    exact (below m ready).trans ((same a active).trans (below m' ready').symm)
  · exact (post_read L B m ready board p hit j).trans
      ((eval_observed live _ _ same p.term _ (reads p hit j)).trans (post_read L B m' ready' board p hit j).symm)

def keptAfter : (ℕ→Prop)→List Pass→ℕ→Prop
  | live,[]=>live
  | live,p::ps=>keptAfter (Written live p.out p.rows) ps

def passReads : (ℕ→Prop)→List Pass→Memory W→Prop
  | _,[],_=>True
  | live,p::ps,m=>(∀i : Fin p.rows,Observed live m (i.val:Word W) p.term) ∧
      passReads (Written live p.out p.rows) ps (p.apply m)

theorem pass_outputs (ps : List Pass) {m m' : Memory W} (live : ℕ→Prop)
    (same : ∀a,live a→m a=m' a) (reads : passReads live ps m) :
    ∀a,keptAfter live ps a→ProtocolRAM.result ps m a=ProtocolRAM.result ps m' a := by
  induction ps generalizing live m m' with
  | nil => exact same
  | cons p ps ih => exact ih _ (scan_words p.out p.rows p.term _ same reads.1) reads.2

/-- The reconciled old stock, cap, overflow, and three new stock columns
are causally determined by the physical debit/credit rows. Solver scratch
is dropped after scatter, except for old cells known to precede it. -/
theorem commit_words (p : RepairHistogram.Columns) (s : RepairHistogram.CommitPlan) (n goods : ℕ)
    (m m' : Memory W) (live : ℕ→Prop) (same : ∀a,live a→m a=m' a)
    (deltas : ∀i : Fin n,Observed live m (i.val:Word W) p.destination ∧
      Observed live m (i.val:Word W) p.credit ∧ Observed live m (i.val:Word W) p.charge)
    (cap : passReads (fun a=>a<s.src ∧ live a)
      (StockAccounts.columns s.clip.base goods s.limit (.lookup s.bank .row))
      (RepairHistogram.result p s.src n m))
    (move : passReads (keptAfter (fun a=>a<s.src ∧ live a)
      (StockAccounts.columns s.clip.base goods s.limit (.lookup s.bank .row)))
      (RepairHistogram.transfers s goods) (RepairHistogram.beforeTransfer p s n goods m)) :
    ∀a,keptAfter (keptAfter (fun a=>a<s.src ∧ live a)
      (StockAccounts.columns s.clip.base goods s.limit (.lookup s.bank .row)))
      (RepairHistogram.transfers s goods) a →
      RepairHistogram.commitOut p s n goods m a=RepairHistogram.commitOut p s n goods m' a := by
  have raw : ∀a,a<s.src ∧ live a →
      RepairHistogram.result p s.src n m a=RepairHistogram.result p s.src n m' a :=
    fun a h=>repair_observed p s.src n m m' live same deltas a h.1 h.2
  exact pass_outputs _ _ (pass_outputs _ _ raw cap) move

end Hierarchy.WireTelescope.ReadBanks

end
end OAI
