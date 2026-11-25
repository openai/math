import OAI.Hierarchy.ProtocolRAMPurchaseMarketImage
import OAI.Hierarchy.ProtocolRAMPurchaseTapeAgree
import OAI.Hierarchy.ProtocolRAMPurchaseGateAgree

namespace OAI
/-! # A frozen purchase pass cannot read future selector pages -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation Calendar
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k cut : ℕ}

private theorem block_cut (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (hd : 1≤d)
    (limit : sh.flagsBase S z d k depth≤ cut) : (sh.L S depth i).endAddress≤ cut :=
  (sh.end_le S depth i hd).trans ((sh.final_after S depth i).trans ((Nat.le_add_right ..).trans limit))

theorem stageImage_below (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (i : Key z d k) (enc : StageEncoding i) {left right : Mem z d}
    (size : Ready S (stage i) (sh.cfg S depth i)) (limit : sh.flagsBase S z d k depth≤ cut)
    (same : Below cut left right) :
    Below cut (sh.stageImage S π depth i enc left) (sh.stageImage S π depth i enc right) := by
  let t:=stage i
  let L:=sh.L S depth i
  let c:=sh.cfg S depth i
  have area:=block_cut sh S depth i hd limit
  have fits:=L.fits (banks t) size.ct size.wide size.degree size.room
  have sFit (a : Fin (2*k)) : (c.stock a).Fits (wordBits z d copies) c.start :=
    ⟨(size.stocks a).2.1,(size.stocks a).2.2.1,(size.stocks a).2.2.2.trans ((Nat.le_add_right _ _).trans size.threshold.2.2)⟩
  have signed:=L.signedFits_of_prefix (banks t) c.threshold c.stock size.directions size.threshold sFit size.room
  have «prefix»:=L.signed_agree (banks t) c.threshold c.stock (axis i) (advisedStage z d π t) enc fits signed area same
  have ready:=L.dispatchReady (banks t) size.ct size.wide size.degree size.room
  exact GateAgree.dispatch «prefix» (sh.desc S depth i) _ ready area

private theorem sweep_below {ι : Type*} {w : ℕ} (f : ι→Memory w→Memory w) (order : List ι)
    (each : ∀i {m n : Memory w},Below cut m n → Below cut (f i m) (f i n))
    {left right : Memory w} (same : Below cut left right) :
    Below cut (ProtocolRAMFrozenSweep.output f order left) (ProtocolRAMFrozenSweep.output f order right) := by
  induction order generalizing left right with
  | nil => exact same
  | cons i order ih => exact ih (each i same)

theorem first_le_flags (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) :
    sh.firstBase≤ sh.flagsBase S z d k depth :=
  (Nat.le_add_right sh.firstBase _).trans (Nat.le_add_right ..)

/-- The same physical mixed-radix encoding certifies the other execution when
the complete retained CT columns agree. -/
theorem ct_below (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (i : Key z d k) (enc : StageEncoding i) {left right : Mem z d}
    (ct : (sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) enc left)
    (heap : heapEnd z d copies≤ cut) (same : Below cut left right) :
    (sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) enc right := by
  have bank (f : Fin 3) (r : Word (wordBits z d copies)) :=
    same.bank (stageBank z d (stageNumber (stage i)) f) r ((stageBank_end z d (stageNumber (stage i)) f).trans heap)
  exact ⟨fun r=>(bank 0 _).symm.trans (ct.group r),fun r=>(bank 1 _).symm.trans (ct.input r),
    fun r=>(bank 2 _).symm.trans (ct.output r)⟩

/-- All words strictly below the current endpoint agree, including dynamic
addresses written by DFS inversion, path decoding, gate assembly and evaluation.
The stock, the price table and the CT banks lie below the cutoff by Incoming. -/
theorem result_below (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (left right fixtureL fixtureR : Mem z d)
    (inputL : sh.Incoming (k:=k) S π depth phase T kind left)
    (inputR : sh.Incoming (k:=k) S π depth phase T kind right)
    (readyL : ∀i : Key z d k,sh.Prepared S depth fixtureL i left)
    (readyR : ∀i : Key z d k,sh.Prepared S depth fixtureR i right)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies)
    (limit : sh.flagsBase S z d k depth≤ cut) (same : Below cut left right) :
    Below cut (sh.result S k depth left) (sh.result S k depth right) := by
  choose enc ct using inputL.ct
  have heap:=inputL.afterCT.trans ((sh.first_le_flags S z d k depth).trans limit)
  have rightCT:=fun i=>sh.ct_below S π depth i (enc i) (ct i) heap same
  rw [sh.result_eq_fullImage S π depth hd phase T kind left fixtureL inputL readyL enc ct room,
    sh.result_eq_fullImage S π depth hd phase T kind right fixtureR inputR readyR enc rightCT room]
  dsimp only [fullImage]
  apply GateAgree.flags (source:=fun i : Key z d k=>sh.flagBank S depth i)
  · exact sweep_below _ (List.finRange _) (fun i {_ _} eq=>
      sh.stageImage_below S π depth hd i (enc i) (inputL.dimensions i) limit eq) same
  · intro i
    obtain ⟨a,b,c⟩:=sh.source_fit S depth i hd room
    exact ⟨a,b,c.trans limit⟩

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
