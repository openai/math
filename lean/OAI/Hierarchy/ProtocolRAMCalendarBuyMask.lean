import OAI.Hierarchy.ProtocolRAMNativeMaskSpace
import OAI.Hierarchy.ProtocolRAMCalendarHalfRead
import OAI.Hierarchy.ProtocolRAMCommittedPortLayout

namespace OAI
/-! # The true buy-mode repair mask disables every physical histogram occurrence -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage ProbeStage.Native PurchaseStage RepairHistogram
open scoped Fin.CommRing Classical
noncomputable section
variable {w q d z k n r edges : ℕ}

theorem MaskSpace.mode (L : Dispatch) (B : Repair q d) (space : MaskSpace L B) (m : Memory w) :
    AttemptGate.actual B.policy (postSnapshot L B m)=AttemptGate.actual B.policy (B.tests.after m) := by
  have bit (t : Bank) (prior : t.base<B.repairBits.base) :
      AttemptGate.bit t (postSnapshot L B m)=AttemptGate.bit t (B.tests.after m) := by
    simp [AttemptGate.bit,Bank.read,postSnapshot,image,fillSegment,not_le.mpr prior]
  simp only [AttemptGate.actual,bit _ space.stop,bit _ space.excess,bit _ space.payload,bit _ space.discrepancy]

/-- Projection of one authentic emitted mask through every real post scan and its verdict. -/
theorem mask_off (L : Dispatch) (B : Repair q d) (space : MaskSpace L B) (m : Memory w)
    (checks : AuditReady (audits L B) (postSnapshot L B m)) (wide : 4≤2^w)
    (mode : AttemptGate.actual B.policy (postSnapshot L B m)≠2) (j : Fin L.candidates) :
    postOutput L B m (B.repairBits.base+j.val)=0 := by
  rw [space.mode L B m] at mode
  change image B.verdict 1 _ (auditOut (audits L B) (postSnapshot L B m)) _=_
  rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (space.verdict j))]
  rw [audit_below _ _ checks _ (space.audit j)]
  change image B.repairBits.base L.candidates (repairMask B) (B.tests.after m) _=_
  rw [ProtocolRAMGeneratedWrite.read_image]
  simp only [repairMask,AttemptGate.ifRepair,AttemptGate.ifMode_eval _ _ _ _ _ _ wide (by decide : 2<4),ite_eq_right mode,Expr.eval,Nat.cast_zero]

/-- Mask ordering in the final priced program derives from the same native
tests and field layout, including the installed discrepancy row count. -/
theorem priced_mask_space (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q n) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin n→Expr) (x : Attempt)
    (capacity : (F x).market.rows≤2^(F x).indexBits) :
    let C := pricedInstalled c finish prices F feeds sink idBase role ids
    MaskSpace (C.layout x) (repair C x) := by
  let C := pricedInstalled c finish prices F feeds sink idBase role ids
  let p := F x
  let L := C.layout x
  let B := repair C x
  let t := (testedBoard p.market.failures p.batch).tests
  have low (j : Fin L.candidates) : p.maskStart+j.val<p.maskStart+2^p.indexBits := by
    exact Nat.add_lt_add_left (j.isLt.trans_le capacity) _
  have col (j : Fin L.candidates) (a : ℕ) : p.maskStart+j.val<
      PostLayout.column p.maskStart p.indexBits L.candidates a := by
    have base := low j
    unfold PostLayout.column PostLayout.startColumns
    omega
  constructor
  · change p.testsStart<p.testsStart+1+(t.excess.rows+1)+(t.payload.rows+1)+(t.discrepancy.rows+1)
    omega
  · change p.testsStart+1+t.excess.rows<p.testsStart+1+(t.excess.rows+1)+(t.payload.rows+1)+(t.discrepancy.rows+1)
    omega
  · change p.testsStart+1+t.excess.rows+1+t.payload.rows<p.testsStart+1+(t.excess.rows+1)+(t.payload.rows+1)+(t.discrepancy.rows+1)
    omega
  · change p.testsStart+1+t.excess.rows+1+t.payload.rows+1+t.discrepancy.rows<
        p.testsStart+1+(t.excess.rows+1)+(t.payload.rows+1)+(t.discrepancy.rows+1)
    omega
  · intro j u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · exact low j
    · obtain ⟨pass,hp,rfl⟩ := List.mem_map.mp hu
      exact writes_after L B _ (col j _) (col j _) (col j _) (fun _=>col j _) (fun _=>col j _)
        (fun _=>col j _) (fun _=>col j _) (fun _=>col j _) pass hp
  · intro j
    exact col j _

namespace StockCommit

/-- The released histograms are read after the price-label pass and after the
native old-stock seed. Neither writes any of the earlier repair-mask words. -/
theorem buy_idle (L : Dispatch) (B : Repair q d) (space : MaskSpace L B) (m : Memory w)
    (a : Area) (s : Sources) (g : LabelSource)
    (wide : 4≤2^w) (rows : L.candidates≤2^w) (padded : L.candidates≤B.repairBits.size)
    (checks : AuditReady (audits L B) (postSnapshot L B m))
    (mode : AttemptGate.actual B.policy (postSnapshot L B m)≠2)
    (before : B.repairBits.base+L.candidates≤g.out) (order : g.out≤a.start)
    (P : let out := postOutput L B m
      PortPlan (fresh a s) (enabledBatch L B) ((a.seed s).apply ((g.pass a.occurrences).apply out)) L.candidates) :
    let out := postOutput L B m
    let source := (a.seed s).apply ((g.pass a.occurrences).apply out)
    ∀ e : Fin a.occurrences,delta (a.columns s) source e=0 := by
  intro out source e
  have mask (j : Fin L.candidates) : source (B.repairBits.base+j.val)=0 := by
    have lo : B.repairBits.base+j.val<g.out := (Nat.add_lt_add_left j.isLt _).trans_le before
    exact (a.seed_frame s _ _ (.inl (lo.trans_le order))).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl lo)).trans
        (mask_off L B space m checks wide mode j))
  have inactive (i : Fin L.candidates) : ¬committed (enabledBatch L B) source (i.val:Word w) := by
    intro active
    have live := active.1.1
    change B.repairBits.read source (i.val:Word w)≠0 at live
    rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le rows),Nat.mod_eq_of_lt (i.isLt.trans_le padded)] at live
    exact live (mask i)
  change delta (fresh a s).columns source e=0
  rw [P.columns]
  apply delta_inactive P.owner P.data P.dest P.ball P.field (enabledBatch L B) P.tabs source e
    (P.enum.symm e).2 P.portRoom P.termRoom P.copyRoom P.sumRoom (P.localIndex e)
  have site : P.ball.eval source (e.val:Word w)=((P.enum.symm e).1.val:Word w) := P.site e
  rw [site]
  exact inactive (P.enum.symm e).1

end StockCommit
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
