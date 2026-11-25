import OAI.Hierarchy.ProtocolRAMCalendarLiveCount
import OAI.Hierarchy.ProtocolRAMPurchaseFlagBinary
import OAI.Hierarchy.ProbeParameters

namespace OAI
/-! # Purchase fees from the archived flag and length words -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {z d k q goods w : ℕ}

/-- The reported length key is the sixth field of this candidate's bought descriptor. -/
theorem purchase_length (C : Chart w q goods) (mem : Memory w) (p h : ℕ)
    (mounted : ready C (.attempt (.outer p h)) (trialState C mem p h))
    (board : Board (C.layout (.outer p h)) (repair C (.outer p h)) w)
    (unit : (repair C (.outer p h)).purchaseLink.lengthCode = .lit 1)
    (j : Fin (C.layout (.outer p h)).candidates) :
    after C (.attempt (.outer p h)) (trialState C mem p h) ((repair C (.outer p h)).boughtFields 5+j.val) = 1 := by
  let a := Attempt.outer p h
  let L := C.layout a
  let B := repair C a
  let x := trialState C mem p h
  let term := buyFields L B 5
  let column : Pass := ⟨B.boughtFields 5,L.candidates,term⟩
  have selected : column ∈ writes L B := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨5,rfl⟩
  have tape := attempt_read C a x mounted board column selected j
  change after C (.attempt a) x (B.boughtFields 5+j.val) = B.purchaseLink.lengthCode.eval
    (postSnapshot L B (prepared C a x)) (j.val:Word w) at tape
  rw [unit] at tape
  exact tape

/-- The money term is read at the same candidate IDs as the archived report.
Each bought link has denominator one in the catalogue length encoding. -/
def purchaseFee (C : Chart w q goods) (mem : Memory w) (p h : ℕ) (Λ exponent concavity cap scale : ℝ) :=
  let a:=Attempt.outer p h
  let B:=repair C a
  let out:=after C (.attempt a) (trialState C mem p h)
  ∑ j : Fin (C.layout a).candidates, ((out (B.purchaseOut+j.val)).val:ℝ)*
    StockCommit.boughtPrice Λ exponent concavity cap scale 1 (out (B.boughtFields 5+j.val)).val

theorem priced_actual_fee {r edges : ℕ} (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (mem : Shelf.Mem z d) (p h total W : ℕ) (Λ exponent concavity cap : ℝ) :
    let C := pricedInstalled c finish prices format feeds sink idBase role ids
    let a := Attempt.outer p h
    let v := (format a).atTime c finish prices a
    let current := trialState C mem p h
    let frozen := v.failures.pass.apply ((guard C a).apply current)
    ∀ (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d),
      v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
      (∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
      ArchiveRoom C mem total → p<total → h<c.outerFuel → v.rows≤2^(format a).batch.decisionBits →
      (format a).batch.purchaseLink.lengthCode = .lit 1 →
      purchaseFee C mem p h Λ exponent concavity cap (dyadicScale W) =
        (Fintype.card (LiveChains v.sampler π v.depth (Shelf.catalogueMarks (k:=k)
          (observedMode C mem p h) v.shelf v.phase v.temperature v.kind frozen)):ℝ) * (Λ*(dyadicScale W)^exponent) := by
  intro C a v current frozen π fixture incoming rom archive hp hh padded unit
  let out := after C (.attempt a) current
  let B := repair C a
  let fee := Λ*(dyadicScale W)^exponent
  obtain ⟨mounted,_,board,_⟩ := archive.outerHead p hp h hh
  have readyMarket : v.ready ((guard C a).apply current) := mounted.2.1
  obtain ⟨_,_,hd,space,_⟩ := readyMarket
  have width : 4≤v.flags := v.shelf.flags_four v.sampler z d k v.depth incoming.afterCT
  have addr : decisionBase (C.layout a)=v.flags := decisionBase_postLayout v.flags v.rows width
  have unitWord : (1:Word (wordBits z d copies)).val=1 := by
    exact Fin.val_cast_of_lt (by have := archive.wide; omega : 1<2^wordBits z d copies)
  have positive : dyadicScale W≠0 := by unfold dyadicScale; positivity
  have each (j : Fin (C.layout a).candidates) :
      (out (B.purchaseOut+j.val)).val≤1 ∧
      StockCommit.boughtPrice Λ exponent concavity cap (dyadicScale W) 1 (out (B.boughtFields 5+j.val)).val=fee := by
    constructor
    · have row := purchase_flag_mode C mem p h mounted board archive.wide (by
        change decisionBase (C.layout a)+v.rows≤_ ∧ _
        rw [addr]
        exact ⟨space.le,(format a).purchase_lanes padded⟩) j
      change (after C (.attempt a) current (B.purchaseOut+j.val)).val≤1
      rw [row]
      by_cases bought : observedMode C mem p h=3
      · rw [ite_eq_left bought,addr]
        exact v.shelf.packed_binary v.sampler π v.depth hd v.phase v.temperature v.kind frozen fixture incoming rom space j
      · simp [bought]
    · have tag := purchase_length C mem p h mounted board unit j
      refine StockCommit.boughtPrice_unit _ _ _ _ _ _ _ ?_ positive
      change ((out (B.boughtFields 5+j.val)).val:ℝ)/1=1
      rw [show out (B.boughtFields 5+j.val)=1 from tag,unitWord]
      norm_num
  have count := priced_purchaseCount_all c finish prices format feeds sink idBase role ids mem p h total
    π fixture incoming rom archive hp hh padded
  rw [←count]
  calc
    purchaseFee C mem p h Λ exponent concavity cap (dyadicScale W) =
        ∑ j : Fin (C.layout a).candidates, if out (B.purchaseOut+j.val)≠0 then fee else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      obtain ⟨bit,price⟩:=each j
      change ((out (B.purchaseOut+j.val)).val:ℝ)*_= _
      rw [price]
      by_cases off : out (B.purchaseOut+j.val)=0
      · simp [off]
      · have nonzero : (out (B.purchaseOut+j.val)).val≠0 := fun h=>off (Fin.ext h)
        have one : (out (B.purchaseOut+j.val)).val=1 := by omega
        simp [off,one]
    _ = (purchaseCount C mem p h:ℝ)*fee := by rw [←Finset.sum_filter]; simp [purchaseCount,out,B,a,current]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
