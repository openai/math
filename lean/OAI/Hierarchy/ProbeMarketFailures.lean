import OAI.Hierarchy.ProbeCommittedMenuRead
import OAI.Hierarchy.ProbeScoreCeiling

namespace OAI
/-! # Every positive pre-repair discrepancy flag commits its actual selected packet -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native PurchaseFrozen PurchaseStage RepairHistogram StockCommit
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {z d k q goods : ℕ}

/-- At a native mode-two attempt the set of affirmative failure words is exactly
the set of committed original rows. Selector validation is the real program's
admission test and ordinary debit sufficiency comes from the chosen packet. -/
theorem Market.committed_iff_threshold (v : Market z d k) (B : Repair q goods)
    (base : Shelf.Mem z d) (ready : v.ready base)
    (owner : B.batch.owner=.row) (installed : B.failedMIS=v.failures.bank)
    (fits : v.rows≤2^wordBits z d copies) (rows : v.rows≤v.failures.rows)
    (cap : v.rows≤v.failures.bank.size) (bits : v.rows≤B.repairBits.size)
    (wide : 4≤2^wordBits z d copies) (cut : v.failures.cut<2^wordBits z d copies)
    (prior : v.failures.base+v.rows≤B.tests.excess.out ∧ v.failures.base+v.rows≤B.tests.payload.out ∧
      v.failures.base+v.rows≤B.tests.discrepancy.out) :
    let m:=v.prefix.after base
    let post:=postSnapshot v.layout B m
    let batch:=enabledBatch v.layout B
    AttemptGate.actual B.policy (B.tests.after m)=2 →
    (∀j : Fin v.rows,batch.valid post (j.val:Word _)) →
    (∀j : Fin v.rows,v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ →
      B.batch.packet.eval post (j.val:Word _)≠0 ∧ ∀p,
        ((B.batch.need p).eval post (j.val:Word _)).val≤((B.batch.stock p).eval post (j.val:Word _)).val) →
    ∀j : Fin v.rows,j∈liveRows batch post v.rows ↔ v.failures.cut<v.failures.value base ⟨j.val,j.isLt.trans_le rows⟩ := by
  intro m post batch mode valid funded j
  refine ⟨v.threshold_of_committed B base ready j owner installed fits rows cap bits wide cut prior,?_⟩
  intro high
  let address:=v.failures.base+j.val
  have lt : address<v.failures.base+v.rows := Nat.add_lt_add_left j.isLt _
  have physical := v.failed_word base ready cut ⟨j.val,j.isLt.trans_le rows⟩
  rw [ite_eq_left high] at physical
  have one : (1:Word (wordBits z d copies))≠0 := by
    intro h
    have h' := congrArg Fin.val h
    have fitsOne : (1 : ℕ) < 2 ^ wordBits z d copies := by omega
    rw [show (1:Word (wordBits z d copies)).val=1 from Fin.val_cast_of_lt fitsOne] at h'
    exact Nat.one_ne_zero h'
  have failure : B.failedMIS.read (B.tests.after m) (B.batch.owner.eval (B.tests.after m) (j.val:Word _))≠0 := by
    rw [installed,owner]
    change (B.tests.after m) (v.failures.base+((j.val:Word (wordBits z d copies)).val%v.failures.bank.size))≠0
    rw [Fin.val_cast_of_lt (j.isLt.trans_le fits),Nat.mod_eq_of_lt (j.isLt.trans_le cap)]
    change (B.tests.after m) address≠0
    rw [AttemptGate.TestBoard.after,B.tests.discrepancy.frame _ _ (lt.trans_le prior.2.2),
      B.tests.payload.frame _ _ (lt.trans_le prior.2.1),B.tests.excess.frame _ _ (lt.trans_le prior.1)]
    intro zero
    apply one
    exact physical.symm.trans zero
  have offer:=funded j high
  have sel : batch.selected post (j.val:Word _) :=
    (post_selected v.layout B m j wide fits bits).2 ⟨⟨mode,failure⟩,offer⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sel,by simpa only [Batch.valid,ite_eq_left sel] using valid j⟩

/-- Only the original record population enters the paid fraction, even when
the underlying raw array has more rows. All inputs here refer to the same
integer score read before the native mask pass. -/
theorem Market.paid_population (v : Market z d k) (B : Repair q goods) (base : Shelf.Mem z d)
    (n precision : ℕ) (ε C : ℝ) (hp : 0<precision) (he : 0<ε) (pos : 0≤C)
    (count : v.rows≤v.failures.rows) (live : Finset (Fin v.rows)) (small : live.card≤n)
    (wordCap : v.failures.cut=⌊2*ε*precision⌋₊) (totalCap : v.failures.globalBound=⌈4*ε*n*precision⌉₊) :
    let word:=fun i : Fin v.rows=>v.failures.value base ⟨i.val,i.isLt.trans_le count⟩
    let batch:=enabledBatch v.layout B
    let post:=postSnapshot v.layout B (v.prefix.after base)
    (∀i∉live,word i=0) → (∀i,(word i:ℝ)/precision≤C) →
    v.failures.globalBound≤∑i,word i →
    (∀i : Fin v.rows,i∈liveRows batch post v.rows ↔ v.failures.cut<word i) →
    ε/(C+1)*n≤(liveRows batch post v.rows).card := by
  intro word batch post absent bounded high trueRows
  have triggered : 4*ε*n*precision≤∑i,(word i:ℝ) := by
    rw [totalCap] at high
    exact (Nat.le_ceil _).trans (by exact_mod_cast high)
  have paid:=Probe.padded_repair_share word (fun i=>(word i:ℝ)/precision) live he hp pos small absent
    bounded (fun _ _=>by simp [he.le]) triggered
  apply paid.1.trans
  exact_mod_cast Finset.card_le_card (show AdaptiveProbe.paddedFailed word (ε:=ε) precision⊆liveRows batch post v.rows by
    intro i hit
    apply (trueRows i).2
    have rank : 2*ε<(word i:ℝ)/precision := (Finset.mem_filter.mp hit).2
    rw [wordCap]
    exact (Nat.floor_lt (by positivity)).2 ((lt_div_iff₀ (Nat.cast_pos.mpr hp)).mp rank))


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
