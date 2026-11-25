import OAI.Hierarchy.ProtocolRAMCalendarReplay
import OAI.Hierarchy.ProtocolRAMCalendarPriced
import OAI.Hierarchy.ProtocolRAMPurchaseLiveCount

namespace OAI
/-! # Purchased chain count in the archived calendar output -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w q goods z d k : ℕ}

private theorem count_true (n : ℕ) (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    cases flag : f 0 <;> simp [Nat.add_comm]

private theorem count_nonzero {n : ℕ} (f : Fin n → Word w) :
    (Finset.univ.filter (fun i => f i ≠ 0)).card =
      (List.ofFn (fun i => decide (f i ≠ 0))).count true := by
  rw [count_true]
  simpa using (Finset.sum_boole (R:=ℕ) (fun i : Fin n => f i ≠ 0) Finset.univ).symm

/-- The postprocessing audit and subsequent stock commit preserve the archived
candidate bit when the observed gate selects purchase. -/
theorem purchase_flag_mode (C : Chart w q goods) (mem : Memory w) (p h : ℕ)
    (mounted : ready C (.attempt (.outer p h)) (trialState C mem p h))
    (board : Board (C.layout (.outer p h)) (repair C (.outer p h)) w)
    (wide : 4≤2^w)
    (bounds : let L:=C.layout (.outer p h); let B:=repair C (.outer p h)
      decisionBase L+L.candidates≤2^w ∧ L.candidates≤2^B.decisionBits ∧
      decisionBase L+L.candidates≤B.tests.excess.out ∧ decisionBase L+L.candidates≤B.tests.payload.out ∧
      decisionBase L+L.candidates≤B.tests.discrepancy.out ∧ decisionBase L+L.candidates≤B.repairBits.base)
    (i : Fin (C.layout (.outer p h)).candidates) :
    after C (.attempt (.outer p h)) (trialState C mem p h) ((repair C (.outer p h)).purchaseOut+i.val) =
      if observedMode C mem p h = 3 then
        prepared C (.outer p h) (trialState C mem p h) (decisionBase (C.layout (.outer p h))+i.val) else 0 := by
  let a := Attempt.outer p h
  let B := repair C a
  let L := C.layout a
  let m := prepared C a (trialState C mem p h)
  rcases mounted with ⟨_,_,_,_,_,_,audit,_,_,_,commit,_,safe⟩
  obtain ⟨fits,padded,excess,payload,discrepancy,sep⟩ := bounds
  let pass : Pass := ⟨B.purchaseOut,L.candidates,buyWord L B⟩
  have inWrites : pass ∈ writes L B := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  change (C.commit a).after (postOutput L B m) (B.purchaseOut+i.val) = _
  exact ((C.commit a).frame _ _ commit (safe pass inWrites i)).trans
    (post_flag L B m audit board wide fits padded i ⟨excess,payload,discrepancy⟩ sep)

/-- A true outer purchase copies the entire contiguous union of the native
greedy decisions into its permanent report. Its cardinality counts the actual
chains on the current signed inventory at the scheduled price. -/
theorem purchaseCount_liveChains (C : Chart (wordBits z d copies) q goods) (mem : Shelf.Mem z d)
    (p h : ℕ) (v : Market z d k) (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d)
    (install : C.layout (.outer p h)=v.layout) («prefix» : C.frozen (.outer p h)=v.prefix)
    (hd : 1≤d) (space : v.flags+v.rows<2^wordBits z d copies)
    (incoming : v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind
      (v.failures.pass.apply ((guard C (.outer p h)).apply (trialState C mem p h))))
    (rom : ∀ i : Key z d k, v.shelf.Prepared v.sampler v.depth fixture i
      (v.failures.pass.apply ((guard C (.outer p h)).apply (trialState C mem p h))))
    (mounted : ready C (.attempt (.outer p h)) (trialState C mem p h))
    (board : Board (C.layout (.outer p h)) (repair C (.outer p h)) (wordBits z d copies))
    (wide : 4≤2^wordBits z d copies) (buy : observedMode C mem p h=3)
    (lanes : let B:=repair C (.outer p h); v.rows≤2^B.decisionBits ∧
      v.flags+v.rows≤B.tests.excess.out ∧ v.flags+v.rows≤B.tests.payload.out ∧
      v.flags+v.rows≤B.tests.discrepancy.out ∧ v.flags+v.rows≤B.repairBits.base) :
    purchaseCount C mem p h = Fintype.card (LiveChains v.sampler π v.depth
      (StripDirectory.actualMarks (k:=k) v.shelf v.phase v.temperature v.kind
        (v.failures.pass.apply ((guard C (.outer p h)).apply (trialState C mem p h))))) := by
  let a := Attempt.outer p h
  let m := trialState C mem p h
  let frozen := v.failures.pass.apply ((guard C a).apply m)
  let out := v.shelf.result v.sampler k v.depth frozen
  have width : 4≤v.flags := v.shelf.flags_four v.sampler z d k v.depth incoming.afterCT
  have base : decisionBase (C.layout a)=v.flags := by
    rw [install]; exact decisionBase_postLayout v.flags v.rows width
  have length : (C.layout a).candidates=v.rows := by rw [install]; rfl
  have image : prepared C a m=out := by rw [prepared,«prefix»]; rfl
  have receipt (r : Fin v.rows) :
      after C (.attempt a) m ((repair C a).purchaseOut+r.val)=out (v.flags+r.val) := by
    let row : Fin (C.layout a).candidates := r.cast length.symm
    have read := purchase_flag_mode C mem p h mounted board wide (by
      change decisionBase (C.layout a)+(C.layout a).candidates≤_ ∧ _
      rw [base,length]
      exact ⟨space.le,lanes⟩) row
    rw [ite_eq_left buy] at read
    change after C (.attempt a) m ((repair C a).purchaseOut+r.val) =
      prepared C a m (decisionBase (C.layout a)+r.val) at read
    rw [image,base] at read
    exact read
  calc
    purchaseCount C mem p h = (Finset.univ.filter (fun r : Fin v.rows => out (v.flags+r.val)≠0)).card := by
      change (Finset.univ.filter (fun r : Fin (C.layout a).candidates =>
        after C (.attempt a) m ((repair C a).purchaseOut+r.val)≠0)).card = _
      rw [length]
      simp only [receipt]
    _ = v.shelf.packedCount v.sampler k v.depth out := count_nonzero (fun r : Fin v.rows => out (v.flags+r.val))
    _ = _ := v.shelf.packedCount_liveChains_result v.sampler π v.depth hd v.phase v.temperature v.kind
      frozen fixture incoming rom space

theorem Format.purchase_lanes (F : Format z d k q goods) (padded : F.market.rows≤2^F.batch.decisionBits) :
    let v:=F.market; let B:=F.board
    v.rows≤2^B.decisionBits ∧ v.flags+v.rows≤B.tests.excess.out ∧
    v.flags+v.rows≤B.tests.payload.out ∧ v.flags+v.rows≤B.tests.discrepancy.out ∧
    v.flags+v.rows≤B.repairBits.base := by
  let checks := (testedBoard F.market.failures F.batch).tests
  let placed := PostLayout.placeTests checks F.testsStart
  have order := PostLayout.tests_separate checks F.testsStart
  change F.testsStart<placed.excess.out ∧ placed.excess.out+placed.excess.rows<placed.payload.out ∧
    placed.payload.out+placed.payload.rows<placed.discrepancy.out ∧
    placed.discrepancy.out+placed.discrepancy.rows+1=PostLayout.afterTests checks F.testsStart at order
  refine ⟨padded,?_⟩
  change F.testsStart≤placed.excess.out ∧ F.testsStart≤placed.payload.out ∧
    F.testsStart≤placed.discrepancy.out ∧ F.testsStart≤PostLayout.afterTests checks F.testsStart
  omega

/-- In the installed priced chart the writer's bounds follow from its assigned
test and mask addresses. The remaining size premise is the declared bit width
of its candidate-index bank. -/
theorem priced_purchaseCount_all {r edges : ℕ} (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (mem : Shelf.Mem z d) (p h total : ℕ) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    let a := Attempt.outer p h
    let v := (format a).atTime c finish prices a
    let current := trialState C mem p h
    let frozen := v.failures.pass.apply ((guard C a).apply current)
    ∀ (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d),
      v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
      (∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
      ArchiveRoom C mem total → p<total → h<c.outerFuel → v.rows≤2^(format a).batch.decisionBits →
      purchaseCount C mem p h = Fintype.card (LiveChains v.sampler π v.depth
        (Shelf.catalogueMarks (k:=k) (observedMode C mem p h) v.shelf v.phase v.temperature v.kind frozen)) := by
  intro C a v current frozen π fixture incoming rom archive hp hh padded
  let F := format a
  obtain ⟨mounted,_,board,_⟩ := archive.outerHead p hp h hh
  have active : v.ready ((guard C a).apply current) := mounted.2.1
  rcases active with ⟨_,_,hd,space,_⟩
  let B := repair C a
  have lanes : v.rows≤2^B.decisionBits ∧ v.flags+v.rows≤B.tests.excess.out ∧
      v.flags+v.rows≤B.tests.payload.out ∧ v.flags+v.rows≤B.tests.discrepancy.out ∧
      v.flags+v.rows≤B.repairBits.base := F.purchase_lanes padded
  by_cases buy : observedMode C mem p h=3
  · rw [Shelf.catalogueMarks_buy _ _ _ _ _ _ buy]
    exact purchaseCount_liveChains C mem p h v π fixture rfl rfl hd space incoming rom
      mounted board archive.wide buy lanes
  · rw [Shelf.card_liveChains_idle _ _ _ _ _ _ _ _ _ buy]
    have width : 4≤v.flags := v.shelf.flags_four v.sampler z d k v.depth incoming.afterCT
    have addr : decisionBase (C.layout a)=v.flags := decisionBase_postLayout v.flags v.rows width
    have empty (j : Fin (C.layout a).candidates) :
        after C (.attempt a) current (B.purchaseOut+j.val)=0 := by
      have bit := purchase_flag_mode C mem p h mounted board archive.wide (by
        change decisionBase (C.layout a)+v.rows≤_ ∧ _
        rw [addr]
        exact ⟨space.le,lanes⟩) j
      exact bit.trans (ite_eq_right buy)
    change (Finset.univ.filter (fun j : Fin (C.layout a).candidates =>
      after C (.attempt a) current (B.purchaseOut+j.val)≠0)).card=0
    simp [empty]

set_option cleanup.letToHave false in
theorem priced_purchaseCount {r edges : ℕ} (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (mem : Shelf.Mem z d) (p h total : ℕ) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    let a := Attempt.outer p h
    let v := (format a).atTime c finish prices a
    let current := trialState C mem p h
    let frozen := v.failures.pass.apply ((guard C a).apply current)
    ∀ (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d),
      v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
      (∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
      ArchiveRoom C mem total → p<total → h<c.outerFuel → v.rows≤2^(format a).batch.decisionBits →
      observedMode C mem p h=3 →
      purchaseCount C mem p h = Fintype.card (LiveChains v.sampler π v.depth
        (StripDirectory.actualMarks (k:=k) v.shelf v.phase v.temperature v.kind frozen)) := by
  intro C a v current frozen π fixture incoming rom archive hp hh padded buy
  have count := priced_purchaseCount_all c finish prices format feeds sink idBase role ids mem p h total
    π fixture incoming rom archive hp hh padded
  have marks := Shelf.catalogueMarks_buy (k:=k) (observedMode C mem p h) v.shelf
    v.phase v.temperature v.kind frozen buy
  exact count.trans (congrArg (fun m => Fintype.card (LiveChains v.sampler π v.depth m)) marks)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
