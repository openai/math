import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProtocolRAMPurchaseSignedDispatch
import OAI.Hierarchy.ProbeAdvisedPurchase

namespace OAI
/-! # Readback of the actual stage's native greedy purchase flags

Physical decision words are measured at the mark interpreter's output addresses.
Deleting padded candidates recovers exactly the advised route's normalized
purchases, and every surviving tile is read at its original CT record ordinal.
-/

namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w n m groups D h k : ℕ} {G : Type*}

def flags (L : Dispatch) (m : Memory w) :=
  List.ofFn (fun i : Fin L.candidates => decide (m (decisionBase L+i.val)≠0))

private theorem same_decision {p q : Prop} [Decidable p] [Decidable q] (eqn : p↔q) :
    decide p=decide q :=by
  by_cases yes : p
  · simp [yes,eqn.mp yes]
  · have absent : ¬q := fun good=>yes (eqn.mpr good)
    simp [yes,absent]

private theorem read_flags (L : Dispatch) (rows : Fin L.candidates→Fin L.depth→Fin L.tiles)
    (mid : Memory w) (ready : DispatchReady L w) (table : PathTable L rows mid) (bit : SignedWords L mid) :
    flags L (dispatchMemory L rows mid) = MarkTape.decisions (paths L rows) (marked L mid) :=by
  apply List.ext_getElem
  · simp only [flags,paths,List.length_ofFn,MarkTape.decisions_length]
  · intro i hi hj
    have small : i<L.candidates:=by simpa only [flags,List.length_ofFn] using hi
    have seen:=(dispatch_exec L rows mid ready table bit).2.2 ⟨i,small⟩
    simp only [flags,List.getElem_ofFn]
    rw [seen,decode_flag ready.width]

/-- The list of true output words and the real surviving row membership agree with
both halves of the unpadded mathematical scan on the stage's live permutation. -/
theorem measured (s : PurchaseTape.Plan D) (b : PurchaseTape.Signed k) (p : Tiles (Fin n) G m)
    (enc : G ↪ Fin groups) (sampler : Fin m→Fin D→Option (Fin m)) (h : ℕ) (mid : Memory w)
    (left : Finset (Fin n))
    (ready : DispatchReady (layout s b n h) w)
    (table : PathTable (layout s b n h) (liveRows p enc sampler h) mid)
    (bit : SignedWords (layout s b n h) mid)
    (set : marked (layout s b n h) mid=left.map Fin.castSuccEmb) :
    let L := layout s b n h
    let rows := liveRows p enc sampler h
    let out := dispatchMemory L rows mid
    let result := scanPaths (PurchaseDFS.candidates (ProtocolRAMPurchaseOwners.successor p enc sampler) h) left
    (dispatch L w).Exec mid out (dispatchClock L) ∧
    (flags L out).count true = result.1.length ∧
    ∀ r : Fin n,out (s.work+4+r.val)=MarkTape.encode w (decide (r∈result.2)) := by
  let L := layout s b n h
  let choice := ProtocolRAMPurchaseOwners.successor p enc sampler
  let rows := liveRows p enc sampler h
  let out := dispatchMemory L rows mid
  let left' := left.map Fin.castSuccEmb
  obtain ⟨run,remaining,bought⟩ := dispatch_exec L rows mid ready table bit
  have pathEq : paths L rows = PurchaseTape.paths p enc sampler h := PurchaseTape.rows_paths ..
  have norm := PurchaseDFS.scan_filled choice h left
  have bits := read_flags L rows mid ready table bit
  let ps : List (List (Fin (n+1))) := paths L rows
  have listed : ps=PurchaseTape.paths p enc sampler h:=pathEq
  have total : (flags L out).count true=(scanPaths ps left').1.length :=by
    refine (congrArg (List.count true) bits).trans ?_
    exact (MarkTape.decisions_count ps (marked L mid)).trans
      (congrArg (fun u : Finset (Fin (n+1))=>(scanPaths ps u).1.length) set)
  refine ⟨run,?_,?_⟩
  · apply total.trans
    rw [listed]
    change (scanPaths ((PurchaseDFS.layout n D h).map (PurchaseDFS.filled choice))
      (left.map Fin.castSuccEmb)).1.length = _
    rw [norm,List.length_map]
  · intro r
    have word := remaining r.castSucc
    rw [set,pathEq] at word
    change out (L.work+4+r.castSucc.val)=MarkTape.encode w (decide (r.castSucc ∈
      (scanPaths ((PurchaseDFS.layout n D h).map (PurchaseDFS.filled choice)) (left.map Fin.castSuccEmb)).2)) at word
    rw [norm] at word
    apply word.trans
    apply congrArg (MarkTape.encode w)
    apply same_decision
    change r.castSucc ∈ ((scanPaths (PurchaseDFS.candidates choice h) left).2.map Fin.castSuccEmb) ↔
      r ∈ (scanPaths (PurchaseDFS.candidates choice h) left).2
    simp [Finset.mem_map,Fin.castSuccEmb_apply]

/-- Changing the numerical group encoding cannot change which live CT row is
reached at a sampler digit. -/
theorem successor_eq {g g' : ℕ} (p : Tiles (Fin n) G m) (u : G ↪ Fin g) (v : G ↪ Fin g')
    (sampler : Fin m→Fin D→Option (Fin m)) :
    ProtocolRAMPurchaseOwners.successor p u sampler = ProtocolRAMPurchaseOwners.successor p v sampler := by
  funext r j
  cases hx : ProtocolRAMPurchaseOwners.successor p u sampler r j with
  | none =>
    cases hy : ProtocolRAMPurchaseOwners.successor p v sampler r j with
    | none => rfl
    | some t =>
      have val := (ProtocolRAMPurchaseOwners.successor_eq_some_iff p u sampler r t j).mpr
        ((ProtocolRAMPurchaseOwners.successor_eq_some_iff p v sampler r t j).mp hy)
      simp [hx] at val
  | some t =>
    exact ((ProtocolRAMPurchaseOwners.successor_eq_some_iff p v sampler r t j).mpr
      ((ProtocolRAMPurchaseOwners.successor_eq_some_iff p u sampler r t j).mp hx)).symm

/-- For the actual advised subdivision, native flag counts are exactly the quantity
in `ProbeStage.advised_purchases_linear`, even when the CT compiler uses a
different fixed numerical encoding for the physical group addresses. -/
theorem measured_advised (S : PurchaseSampler) {z d : ℕ} (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d)
    (enc : (stageAt z d t).Group ↪ Fin groups) (s : PurchaseTape.Plan S.degree) (b : PurchaseTape.Signed k)
    (depth : ℕ) (mid : Memory w) (left : Finset (Fin (2^z)))
    (ready : DispatchReady (layout s b (2^z) depth) w)
    (table : PathTable (layout s b (2^z) depth) (liveRows (advisedStage z d π t) enc (portDigits (S.rows _)) depth) mid)
    (bit : SignedWords (layout s b (2^z) depth) mid)
    (set : marked (layout s b (2^z) depth) mid=left.map Fin.castSuccEmb) :
    let L := layout s b (2^z) depth
    let rows := liveRows (advisedStage z d π t) enc (portDigits (S.rows _)) depth
    let out := dispatchMemory L rows mid
    (dispatch L w).Exec mid out (dispatchClock L) ∧
    (flags L out).count true=(advisedPurchases S π t depth left).1.length ∧
      ∀ r : Fin (2^z),out (s.work+4+r.val)=MarkTape.encode w (decide (r∈(advisedPurchases S π t depth left).2)) := by
  have val := (measured s b (advisedStage z d π t) enc (portDigits (S.rows _)) depth mid left ready table bit set)
  have geo := successor_eq (advisedStage z d π t) enc (Fintype.equivFin (stageAt z d t).Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows _))
  refine ⟨val.1,by simpa only [advisedPurchases,geo] using val.2.1,?_⟩
  intro r
  refine (val.2.2 r).trans (congrArg (MarkTape.encode w) (same_decision ?_))
  simp only [advisedPurchases,geo]

/-- Initial conditions mention the resident CT fields, signed stock and static
ROM only. The CPU writes the entire H-chain table, computes signs and decisions,
and returns the physical purchase count of the advised route. -/
theorem execute_advised (S : PurchaseSampler) {z d : ℕ} (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d)
    (enc : (stageAt z d t).Group ↪ Fin groups) (s : PurchaseTape.Plan S.degree) (b : PurchaseTape.Signed k)
    (depth : ℕ) (j : Fin (2*k)) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (mem : Memory w)
    (size : PurchaseTape.Fits s w (2^z) groups (stageAt z d t).span depth)
    (bounds : PurchaseTape.SignedFits s b w (2^z))
    (input : PurchaseTape.Loaded s (advisedStage z d π t) enc (portDigits (S.rows _)) depth mem)
    (table : PurchaseMarks.Table phase T k kind b.threshold mem)
    (separate : s.packed+3*(PurchaseTape.count (2^z) S.degree depth*(4*(depth+1)+3)) ≤ s.work)
    (room : decisionBase (layout s b (2^z) depth) + PurchaseTape.count (2^z) S.degree depth<2^w) :
    let L := layout s b (2^z) depth
    let tiles := advisedStage z d π t
    let rows := liveRows tiles enc (portDigits (S.rows _)) depth
    let out := dispatchMemory L rows (PurchaseTape.signedOut s b j tiles enc depth mem)
    let left := PurchaseMarks.stratum (n:=2^z) phase T kind b.threshold b.stock mem j
    ((PurchaseTape.signedPrefix s b j w (2^z) groups (stageAt z d t).span depth).seq (dispatch L w)).Exec mem out
      (PurchaseTape.signedTicks s (2^z) groups (stageAt z d t).span depth k + dispatchClock L) ∧
    (flags L out).count true=(advisedPurchases S π t depth left).1.length ∧
    ∀ r : Fin (2^z), out (s.work+4+r.val)=MarkTape.encode w (decide (r∈(advisedPurchases S π t depth left).2)) := by
  let L := layout s b (2^z) depth
  let tiles := advisedStage z d π t
  let mid := PurchaseTape.signedOut s b j tiles enc depth mem
  let left := PurchaseMarks.stratum (n:=2^z) phase T kind b.threshold b.stock mem j
  obtain ⟨beginRun,rows,rom,marks⟩ := PurchaseTape.signed_columns_run s b phase T kind j tiles enc
    (portDigits (S.rows _)) depth mem size bounds input table
  have prepared := ready_of_fits s b size bounds separate room
  obtain ⟨binary,exactMarks⟩ := signed_of_resident L mid (left.map Fin.castSuccEmb) size.wide marks
  obtain ⟨dispatch,number,remainder⟩ := measured_advised S π t enc s b depth mid left prepared ⟨rows,rom⟩ binary exactMarks
  refine ⟨?_,number,remainder⟩
  intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
  exact Procedure.Exec.then beginRun dispatch machine pc reg slots exit rom advice cfg rawMem enter same

end
end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
