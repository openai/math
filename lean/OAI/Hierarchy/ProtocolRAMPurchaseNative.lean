import OAI.Hierarchy.ProtocolRAMPurchaseRuntimeOperands
import OAI.Hierarchy.ProtocolRAMPurchaseCalendarROM
import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseCT
import OAI.Hierarchy.ProbeStagePhysicalOrdinal
import OAI.Hierarchy.ProtocolRAMPurchaseSamplerBack

namespace OAI
/-! # Subdivision and signed sampler purchase as one executable procedure

The only low input words are permutation records. The initial public tape has
the sampler, address and threshold tables in disjoint regions above the CT heap.
Every signed decision and every remaining tile is read back from the composed
program, with the same physical integer stock values as before subdivision.
-/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def initial (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (phase : PhasePrice) (T : ℝ)
    (kind : ℕ) (raw : Memory (wordBits z d copies)) :=
  let L := geom S t c
  let quote := PurchaseMarks.mount phase T k kind c.threshold raw
  inputTape z d _ (L.data (S.rows L.sockets) (reverseDigits S L.sockets) quote)

def program (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (j : Fin (2*k)) :=
  let s := embedded S t c
  let b := sign S t c
  let w := wordBits z d copies
  (subdivisionProgram z d).seq ((PurchaseTape.signedPrefix s b j w (2^z)
    (Fintype.card (stageAt z d t).Group) (stageAt z d t).span c.depth).seq
    (PurchaseStage.dispatch (PurchaseStage.layout s b (2^z) c.depth) w))

def ticks (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) :=
  let s := embedded S t c
  let b := sign S t c
  subdivisionConstant d*2^z+(PurchaseTape.signedTicks s (2^z) (Fintype.card (stageAt z d t).Group)
    (stageAt z d t).span c.depth k + PurchaseStage.dispatchClock (PurchaseStage.layout s b (2^z) c.depth))

private theorem eq_decide_of_iff {p q : Prop} [Decidable p] [Decidable q] (eqn : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp,eqn.mp hp]
  · have hq : ¬q := fun h => hp (eqn.mpr h)
    simp [hp,hq]

/-- The subdivision, sign computation, canonical DFS and NAND interpreter execute
chronologically. Returned words measure the output of the literal advised route. -/
theorem run (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (j : Fin (2*k))
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (π : Equiv.Perm (Fin (2^z))) (raw : Memory (wordBits z d copies))
    (read : ∀ i : Fin (2^z), raw i.val=((π i).val:Word _)) (hd : 1≤d)
    (ready : Ready S t c) :
    let L := PurchaseStage.layout (embedded S t c) (sign S t c) (2^z) c.depth
    let left := PurchaseMarks.stratum (n:=2^z) phase T kind c.threshold c.stock raw j
    ∃ out, (program S t c j).Exec (initial S t c phase T kind raw) out (ticks S t c) ∧
      (PurchaseStage.flags L out).count true=(advisedPurchases S π t c.depth left).1.length ∧
      ∀ r : Fin (2^z),out (L.work+4+r.val)=MarkTape.encode (wordBits z d copies)
        (decide (r∈(advisedPurchases S π t c.depth left).2)) := by
  let L := geom S t c
  let s := embedded S t c
  let b := sign S t c
  let rows := S.rows L.sockets
  let back := reverseDigits S L.sockets
  let quote := PurchaseMarks.mount phase T k kind c.threshold raw
  let setup := L.data rows back quote
  let input := inputTape z d _ setup
  let mid := images z d input (rounds d)
  have low := ready.threshold.2.2
  have inputRead (i : Fin (2^z)) : setup i.val=((π i).val:Word _) := by
    have before := i.isLt.trans_le ready.raw
    rw [show setup i.val=quote i.val from L.data_prefix rows back quote _ (by change i.val<c.start; omega)]
    simpa [quote,PurchaseMarks.mount,fillSegment,not_le.mpr before] using read i
  obtain ⟨route,done⟩ := native_linear_run hd π setup inputRead (physical_ordinal hd π)
  have high (a : ℕ) (ha : L.start≤a) : mid a=L.data rows back quote a :=
    images_above setup done (by change c.start≤a at ha; have := ready.heap; omega)
  obtain ⟨enc,ct⟩ := resident π t c.start S.degree c.depth c.first input done
  have actual := L.loaded_after (banks t) (advisedStage z d π t) enc rows back quote mid high ready.ct ct ready.sockets ready.room
  have fits := L.fits (banks t) ready.ct ready.wide ready.degree ready.room
  have stockFits (v : Fin (2*k)) : (c.stock v).Fits (wordBits z d copies) c.start :=
    ⟨(ready.stocks v).2.1,(ready.stocks v).2.2.1,(ready.stocks v).2.2.2.trans (by omega)⟩
  have signedFits := L.signedFits_of_prefix (banks t) c.threshold c.stock ready.directions ready.threshold stockFits ready.room
  have held (bank : Bank) (lo : heapEnd z d copies≤bank.base) (fit : bank.Fits (wordBits z d copies) L.start) (r : Word _) :
      bank.read mid r=bank.read quote r := by
    change mid (bank.base+r.val%bank.size)=quote _
    exact (images_above setup done (lo.trans (Nat.le_add_right ..))).trans
      (L.data_prefix rows back quote _ ((Nat.add_lt_add_left (Nat.mod_lt _ fit.1) _).trans_le fit.2.2))
  have table : PurchaseMarks.Table phase T k kind c.threshold mid := fun r=>
    (held c.threshold ready.heap ready.threshold r).trans (PurchaseMarks.mount_table phase T k kind c.threshold raw r)
  obtain ⟨_,_,_,_,_,_,_,sep,room⟩ := L.regions
  have ⟨act,flags,remaining⟩ := PurchaseStage.execute_advised S π t enc s b c.depth j phase T kind mid
    fits signedFits actual table sep.le ready.room
  have unchanged (r : Word (wordBits z d copies)) : PurchaseMarks.tested phase T kind c.threshold c.stock mid r=
      PurchaseMarks.tested phase T kind c.threshold c.stock raw r := by
    funext v
    have addr := Nat.mod_lt r.val (ready.stocks v).2.1
    have bound := (ready.stocks v).2.2.2
    have small : (c.stock v).base+r.val%(c.stock v).size<c.threshold.base := by omega
    simp only [PurchaseMarks.tested,held _ (ready.stocks v).1 (stockFits v) r]
    simp [Bank.read,quote,PurchaseMarks.mount,fillSegment,not_le.mpr small]
  have identical : PurchaseMarks.stratum (n:=2^z) phase T kind c.threshold c.stock mid j=
      PurchaseMarks.stratum phase T kind c.threshold c.stock raw j := by simp only [PurchaseMarks.stratum,unchanged]
  let tiles := advisedStage z d π t
  let out := PurchaseStage.dispatchMemory (PurchaseStage.layout s b (2^z) c.depth)
    (PurchaseStage.liveRows tiles enc (AdaptiveProbe.portDigits (S.rows _)) c.depth)
    (PurchaseTape.signedOut s b j tiles enc c.depth mid)
  refine ⟨out,route.then act,?_,?_⟩
  · change (PurchaseStage.flags (PurchaseStage.layout s b (2^z) c.depth) out).count true = _
    exact flags.trans (congrArg (fun xs => (advisedPurchases S π t c.depth xs).1.length) identical)
  · intro r
    change out (s.work+4+r.val) = _
    refine (remaining r).trans (congrArg (MarkTape.encode _) (eq_decide_of_iff ?_))
    change (r ∈ (advisedPurchases S π t c.depth
      (PurchaseMarks.stratum phase T kind c.threshold c.stock mid j)).2) ↔ _
    rw [identical]

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
