import OAI.Hierarchy.GridPassageMaskExec

namespace OAI
/-! # Loaded native procedure for direction-dependent first-passage tables -/

namespace Hierarchy.GridPassageRAMMask
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open GridLens GridPassageRAMPadIndex
open GridPassageRAMRow (AddressMap DecodeReads rankIn cursor)
open scoped Classical Fin.CommRing

variable {w k n E : ℕ}

private theorem driver (v : Parameters w) (rows : ℕ) (fit : rows < 2^w)
    (limit : v 0 = (rows : Word w)) (mem : ℕ → Memory w)
    (changeRow : ∀ i<rows, wordStep v (i : Word w) (mem i) = mem (i+1)) :
    (procedure v).Exec (mem 0) (mem rows) (3+rows*39) := by
  intro P R K M pc reg pub exit installed data cfg input entry same
  subst input
  change Fin 17 ↪ Fin R at reg
  change Fin 9 → Fin K at pub
  change ∀ j : Fin 9, M.publicData (pub j) = v j at data
  have hv : (M.publicData ∘ pub : Fin 9 → Word w) = v := funext data
  obtain ⟨out,run,done⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 0 M pc reg pub exit installed
    rows fit ((data 0).trans limit) mem (fun i hi state rs cur bound => by
      obtain ⟨es,rs',tr,inc,keep⟩ := row_trace reg pub M.publicData state rs (mem i)
      rw [hv,cur,changeRow i hi] at tr
      exact ⟨es,rs',tr,
        by simpa only [cur,Nat.cast_add,Nat.cast_one] using inc,keep.trans bound⟩) cfg entry
  exact ⟨_,le_rfl,out,_,run,done,rfl⟩

def program (a : AddressMap) (w compact k n E B : ℕ) : Procedure w :=
  (a.program w k n E B).seq (procedure (parameters a w compact k n B))

/-- The three real native budgets sum to a linear number of rail-position visits when the
line inventory covers one padded direction bank for each cell. -/
theorem cost_le (bins rows B : ℕ) (positive : 1 ≤ B) (inventory : bins*B ≤ rows) :
    4+bins*6+(3+rows*55)+(3+(bins*B)*39) ≤ 10+rows*100 := by
  have hb : bins ≤ bins*B := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left bins positive
  omega

/-- Execute the physical zero fill, rail sweep and padded-slot correction; all remaining inputs
are the contents of the four immutable geometry pages and the directions' widths and strides. -/
theorem exec (a : AddressMap) (compact B : ℕ) (direction : Fin E → Fin k)
    (row : Fin E → Fin k → Fin (n+1)) (touch : Fin E → Option (Fin (n+1))) (width : Fin k → ℕ)
    (fits : a.Fits w k n E B) (widthsBelow : compact+6+k ≤ a.out.counter) (pad : ∀ j, width j ≤ B)
    (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (widths : ∀ j : Fin k, input (compact+6+j.val) = (width j : Word w))
    (powers : ∀ j : Fin k, input (a.powers+j.val) = (((n+1)^j.val : ℕ) : Word w)) :
    (program a w compact k n E B).Exec input (finalMemory direction row touch width a B input)
      (4+((n+1)^k*k)*6+(3+E*(n+1)*55)+(3+((n+1)^k*k*B)*39)) := by
  let first := a.finalMemory k n E B input
  let eraseAt := target direction row touch width a.out.mark B
  let mem := erased eraseAt first
  have state := a.final_correct direction row touch B fits input loaded
  have cBound := fits.separated.counts
  have oBound := fits.separated.choices
  have mBound := fits.upper
  have pBound := fits.powers
  have advanceRow : ∀ i < (n+1)^k*k*B,
      wordStep (parameters a w compact k n B) (i : Word w) (mem i) = mem (i+1) := by
    intro i hi
    obtain ⟨⟨⟨x,j⟩,r⟩,eq,_⟩ := decode i hi
    subst i
    let i := ordinal x j r
    let s := untouchedRails direction row touch x j
    let count := min B s.card
    let label := if h : r.val < s.card then (s.orderEmbOfFin rfl ⟨r.val,h⟩).val else 0
    have jBound := j.isLt
    have iBound := ordinal_lt x j r
    have bBound : key x j < (n+1)^k*k := by
      change (finFunctionFinEquiv x).val*k+j.val < _
      have digits := (finProdFinEquiv (finFunctionFinEquiv x,j)).isLt
      change j.val+k*(finFunctionFinEquiv x).val < (n+1)^k*k at digits
      simpa only [Nat.add_comm,Nat.mul_comm] using digits
    have wFit := (pad j).trans_lt fits.capacity
    have cFit : count<2^w := (Nat.min_le_left ..).trans_lt fits.capacity
    have low (p : ℕ) (hp : p<a.out.mark) : mem i p = first p :=
      erased_below eraseAt first a.out.mark i p (fun u _ z hz => (target_range direction row touch width _ _ _ _ hz).1) hp
    have wf : compact+6+j.val < a.out.counter := by omega
    have pf : a.powers+j.val < a.out.counter := by omega
    have reads : MaskReads (mem i) a.out.counter a.out.chosen compact a.powers (width j) count label x j r := by
      constructor
      · exact (low _ (by omega)).trans ((state.input _ wf).trans (widths j))
      · rw [low _ (by omega)]
        apply Fin.ext
        exact (a.final_counter direction row touch B fits input loaded x j).trans (Fin.val_cast_of_lt cFit).symm
      · exact (low _ (by omega)).trans ((state.input _ pf).trans (powers j))
      · intro gate
        have hr := gate.2.trans_le (Nat.min_le_right B s.card)
        let e := s.orderEmbOfFin rfl ⟨r.val,hr⟩
        have he : e ∈ s := s.orderEmbOfFin_mem rfl _
        have rank : rankIn direction row touch x j e = r.val :=
          GridPassageRank.rank_orderEmbOfCardLe s le_rfl ⟨r.val,hr⟩
        have chose := a.final_chosen_of_rank direction row touch B fits input loaded x j e he (by simpa only [rank] using r.isLt)
        rw [low _ (by omega)]
        simpa only [first,i,ordinal,key,rank,label,dite_eq_left hr,Nat.add_assoc] using chose
    have room : MaskRoom w a.out.counter a.out.chosen compact a.powers a.out.mark (width j) count label x j r := by
      refine ⟨fits.capacity,by omega,fits.radix,fits.extent,by omega,wFit,cFit,by omega,by omega,by omega,fun _ => by omega,?_⟩
      intro gate
      have hr := gate.2.trans_le (Nat.min_le_right B s.card)
      let e := s.orderEmbOfFin rfl ⟨r.val,hr⟩
      have ed : label = e.val := dite_eq_left hr
      have et : e.val*(n+1)+(x j).val < E*(n+1) := calc
        _ < e.val*(n+1)+(n+1) := Nat.add_lt_add_left (x j).isLt _
        _ = (e.val+1)*(n+1) := (Nat.succ_mul ..).symm
        _ ≤ E*(n+1) := Nat.mul_le_mul_right _ e.isLt
      rw [ed]
      omega
    have step := maskDecode ((n+1)^k*k*B) a.out.counter a.out.chosen compact a.powers a.out.mark
      (width j) count label x j r (mem i) reads room
    change wordStep _ (i : Word w) (mem i) = erased eraseAt first (i+1)
    change wordStep (values w ((n+1)^k*k*B) B k (n+1) a.out.counter a.out.chosen compact a.powers a.out.mark)
      (ordinal x j r : Word w) (mem i) = _
    rw [step]
    have ti : eraseAt i = removeAt direction row touch width a.out.mark x j r := target_slot ..
    by_cases gate : width j ≤ r.val ∧ r.val < s.card
    · have gc : width j ≤ r.val ∧ r.val < count := ⟨gate.1,lt_min r.isLt gate.2⟩
      have ht : eraseAt i = some (a.out.mark+cursor label (x j)) := by simpa only [removeAt,s,dite_eq_left gate,label,dite_eq_left gate.2] using ti
      simp only [ite_eq_left gc,erased,ht,cursor,Nat.add_assoc,mem]
    · have gc : ¬(width j ≤ r.val ∧ r.val < count) := fun h => gate ⟨h.1,h.2.trans_le (Nat.min_le_right ..)⟩
      have ht : eraseAt i = none := by simpa only [removeAt,s,dite_eq_right gate] using ti
      simp only [ite_eq_right gc,erased,ht,mem]
  apply Procedure.Exec.then (A := a.program w k n E B) (B := procedure (parameters a w compact k n B))
    (b := first)
  · exact a.exec k n E B fits input
  · exact driver (parameters a w compact k n B) _ (by omega) rfl mem advanceRow


end Hierarchy.GridPassageRAMMask

end OAI
