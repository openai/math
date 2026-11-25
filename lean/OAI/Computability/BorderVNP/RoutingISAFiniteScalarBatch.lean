import OAI.Computability.BorderVNP.RoutingISAFiniteScalarRow
import OAI.Computability.BorderVNP.RoutingISAAddressProof
import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceProduct
import Mathlib.Algebra.BigOperators.Intervals

/-! # Chronological finite-field scalar calls after the owned cell validators

The fixed stage reloads the prepared compact task table, obtains each actual
tail width by its global call-row number, and executes one field routine.
Its sole successful chronology includes all ordinary packing stores and one
field-returning burst per owned cell, with no new choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FiniteScalarBatch

open VPVNP.BurstRAM CellDispatch Finset

/-- Reload the concrete frame and task-directory operands after the signed validators. -/
def setup : Code := .block [readFrame 40 62 63 30,readFrame 41 62 63 89,readFrame 42 62 63 90,
  readFrame 50 62 63 14,readFrame 51 62 63 92,.constant 52 7,.binary .add 51 51 52,.load 51 51,
  .constant 52 3,.constant 43 0,.constant 44 7,.constant 47 1]

/-- Fixed scalar suffix entry with one loop iteration per owned typed task. -/
def code : Code := .seq setup (.whileLt 43 42 body)

/-- The scalar suffix writes only packed count words into the existing cell scratch arenas. -/
def written {w : ℕ} (m : Memory w) (rows : ℕ → Row) : ℕ → Memory w
  | 0 => m
  | i+1 => (rows i).image (written m rows i)

/-- Recognize a native private call, including a call on a zero-length interval. -/
def isBurst {w : ℕ} (e : TeamRAM.Event w) : Bool := match e.action with
  | .burst .. => true
  | .ordinary .. => false

/-- Every private call in the scalar suffix, in instruction order. -/
def bursts {w : ℕ} (es : List (TeamRAM.Event w)) := es.filter isBurst

/-- The one genuine scalar return at the indicated owned cell. -/
def Row.event (r : Row) (w : ℕ) := FiniteScalarCall.event r.task.cell.scratchBase (r.words w)

private theorem noBursts {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c s m es t mt} (run : Runs pub mac c s m es t mt) (h : c.deterministic=true) : bursts es=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  obtain ⟨p,action⟩ := FiniteDiagonal.ordinary_of_deterministic run h e he
  simp [isBurst,action]

private theorem rowBursts {w : ℕ} (r : Row) : bursts [r.event w,tick w] = [r.event w] := rfl

private theorem setup_run {w table count calls tails : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame : (pub 0).val+92 < 2^w)
    (width : (m ((pub 0).val+30)).val=w) (tableWord : (m ((pub 0).val+89)).val=table)
    (len : (m ((pub 0).val+90)).val=count) (callWord : (m ((pub 0).val+14)).val=calls)
    (control : (m ((pub 0).val+92)).val+7 < 2^w) (tailWord : (m ((m ((pub 0).val+92)).val+7)).val=tails) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧ Ready table count calls tails 0 t := by
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide:=true}) [setup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,readings]
    have nz : w ≠ 0 := by rintro rfl; simp at frame
    omega
  obtain ⟨es,t,r,c,hr⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨_,t,r,c,?_⟩
  change (readings t 40=w ∧ readings t 41=table ∧ readings t 42=count ∧ readings t 43=0 ∧
    readings t 44=7 ∧ readings t 47=1) ∧ readings t 50=calls ∧ readings t 51=tails ∧ readings t 52=3
  rw [hr]
  simp (config := {decide:=true}) [setup,readFrame,Code.block,Code.evalNat,addressOp,readings,width,tableWord,len,callWord,tailWord]

private theorem loop {w table count calls tails : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (m : Memory w) (rows : ℕ → Row) (hw : 0 < w) (space : table+7*count ≤ 2^w)
    (source : ∀ i < count, Stored (rows i) (written m rows i) table calls tails i)
    (fit : ∀ i < count, Fits (rows i) w tails)
    (scalar : ∀ i < count, ∀ bs, mac 1 ((rows i).words w) bs = if bs.isEmpty then some .plus else none)
    (i : ℕ) (hi : i ≤ count) (s : Bank w) (ready : Ready table count calls tails i s) :
    ∃ es t, Runs pub mac (.whileLt 43 42 body) s (written m rows i) es t (written m rows count) ∧
      traceCost es ≤ (∑ j ∈ Ico i count, ((rows j).cost w+1))+1 ∧
      bursts es = (List.range' i (count-i)).map (fun j => (rows j).event w) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ fs v mv, Runs pub mac (.whileLt 43 42 body) s (written m rows i) fs v mv →
        fs=es ∧ v=t ∧ mv=written m rows count := by
  have hindex := ready.1.2.2.2.1
  have hcount := ready.1.2.2.1
  by_cases endRow : i=count
  · rw [endRow]
    have guard : ¬ s 43 < s 42 := show ¬ (s 43).val < (s 42).val by omega
    refine ⟨[tick w],s,.whileDone guard,?_,?_,?_,fun _ _ _ r => while_last r guard⟩
    · change 1 ≤ _; omega
    · simp [bursts,isBurst,tick]
    · simp [tick]
  · have lt : i<count := by omega
    have guard : s 43 < s 42 := show (s 43).val < (s 42).val by omega
    obtain ⟨pre,u,v,ordinary,first,cost,next,unique⟩ := body_run (pub:=pub) (mac:=mac) (rows i) s
      (written m rows i) hw ready (source i lt) (fit i lt) lt space (scalar i lt)
    let one := pre++[(rows i).event w,tick w]
    change Runs pub mac body s (written m rows i) one v (written m rows (i+1)) at first
    obtain ⟨ys,t,rest,cy,byes,clean,only⟩ := loop pub mac m rows hw space source fit scalar (i+1) lt v next
    refine ⟨_,t,.whileStep guard first rest,?_,?_,?_,?_⟩
    · change 1+traceCost (one++ys) ≤ _
      rw [show traceCost (one++ys) = traceCost one+traceCost ys from VPVNP.RAMBuckets.cost_append ..,sum_eq_sum_Ico_succ_bot lt]
      change traceCost one ≤ (rows i).cost w at cost
      omega
    · have bp := noBursts ordinary (by decide)
      have br := rowBursts (w:=w) (rows i)
      have hr : count-i = (count-(i+1))+1 := by omega
      simp only [bursts] at bp br byes ⊢
      have firstFalse : isBurst (tick w) = false := rfl
      simp only [List.filter_cons,firstFalse,Bool.false_eq_true,ite_false,one,List.filter_append,bp,br,byes,List.nil_append,hr,
        List.range'_succ,List.map_cons,List.singleton_append]
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨rfl,rfl⟩
      · rcases List.mem_append.mp he with h | h
        · rcases List.mem_append.mp h with h | h
          · exact ordinary.unsigned_events (by decide) _ h
          · rcases List.mem_cons.mp h with rfl | h
            · exact ⟨rfl,rfl⟩
            · obtain rfl := List.mem_singleton.mp h; exact ⟨rfl,rfl⟩
        · exact clean _ h
    · intro fs b mb r
      obtain ⟨gs,a,ma,zs,rfl,step,ending⟩ := while_next r guard
      obtain ⟨rfl,rfl,rfl⟩ := unique _ _ _ step
      obtain ⟨rfl,rfl,rfl⟩ := only _ _ _ ending
      exact ⟨rfl,rfl,rfl⟩
termination_by count-i

/-- The actual native suffix has one returning chronology. The private calls are
exactly the ordered fixed-macro events on the bit-major reports, with no further
private guesses and with total RAM charge linear in the true supplied tail sizes. -/
theorem run {w table count calls tails : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (rows : ℕ → Row) (frame : (pub 0).val+92 < 2^w)
    (width : (m ((pub 0).val+30)).val=w) (tableWord : (m ((pub 0).val+89)).val=table)
    (len : (m ((pub 0).val+90)).val=count) (callWord : (m ((pub 0).val+14)).val=calls)
    (control : (m ((pub 0).val+92)).val+7 < 2^w) (tailWord : (m ((m ((pub 0).val+92)).val+7)).val=tails)
    (space : table+7*count ≤ 2^w)
    (source : ∀ i < count, Stored (rows i) (written m rows i) table calls tails i)
    (fit : ∀ i < count, Fits (rows i) w tails)
    (scalar : ∀ i < count, ∀ bs, mac 1 ((rows i).words w) bs = if bs.isEmpty then some .plus else none) :
    ∃ es t, Runs pub mac code s m es t (written m rows count) ∧
      traceCost es ≤ setup.slots+(∑ j ∈ Finset.range count, ((rows j).cost w+1))+1 ∧
      bursts es = (List.range count).map (fun j => (rows j).event w) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ fs v mv, Runs pub mac code s m fs v mv → fs=es ∧ v=t ∧ mv=written m rows count := by
  obtain ⟨gs,u,init,cs,ready⟩ := setup_run pub mac s m frame width tableWord len callWord control tailWord
  have hw : 0 < w := by cases w with
    | zero => simp at frame
    | succ w => exact Nat.zero_lt_succ w
  obtain ⟨ys,t,rest,cy,bs,cl,only⟩ := loop pub mac m rows hw space source fit scalar 0 (Nat.zero_le _) u ready
  refine ⟨_,t,init.seq rest,?_,?_,?_,?_⟩
  · rw [show traceCost (gs++ys)=traceCost gs+traceCost ys from VPVNP.RAMBuckets.cost_append ..]
    rw [Nat.Ico_zero_eq_range] at cy
    omega
  · have zero := noBursts init (by decide)
    change bursts (gs++ys) = _
    rw [show bursts (gs++ys) = bursts gs++bursts ys from List.filter_append ..,zero,List.nil_append,bs]
    simp [List.range_eq_range']
  · exact fun e he => (List.mem_append.mp he).elim (init.unsigned_events (by decide) e) (cl e)
  · intro fs v mv r
    obtain ⟨zs,a,ma,ss,rfl,first,ending⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := init.unique_of_deterministic (by decide) first
    obtain ⟨rfl,rfl,rfl⟩ := only _ _ _ ending
    exact ⟨rfl,rfl,rfl⟩

end RoutingISA.FiniteScalarBatch

end BorderVNP
end Computability
end OAI
