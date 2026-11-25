import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProbeLiveSlots

namespace OAI
/-! # Number of actual retained chains in the stored signed decisions -/
namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
open AdaptiveProbe Filter
open scoped BigOperators
noncomputable section
variable {z d k : ℕ}
/-- Count nonzero words across the entire contiguous purchase decision table. -/
def packedCount (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (out : Mem z d) : ℕ :=
  let base := sh.flagsBase S z d k depth
  (List.ofFn fun r : Fin (count z d k*paths z S.degree depth) => decide (out (base+r.val)≠0)).count true

/-- Reading the packed decision table recovers the total number of advised
purchases across all stages and signs for the same frozen commodity stock. -/
theorem packedCount_eq (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen out : Mem z d)
    (words : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
      out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)=
        MarkTape.encode (wordBits z d copies)
          ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp))) :
    sh.packedCount S k depth out = ∑ t : StageAt z d, ∑ j : Fin (2*k),
      (advisedPurchases S π t depth (sh.marked phase T kind frozen (key t j))).1.length := by
  let R := paths z S.degree depth
  let base := sh.flagsBase S z d k depth
  let f := fun i : Key z d k => (advisedPurchases S π (stage i) depth (sh.marked phase T kind frozen i)).1.length
  have width : 0 < wordBits z d copies := by unfold wordBits; omega
  have slab (i : Key z d k) :
      (List.ofFn fun r : Fin R => decide (out (base+(i.val*R+r.val)) ≠ 0)) =
        sh.decisions S π depth phase T kind frozen i := by
    apply List.ext_getElem
    · simp [R]
    · intro r hr hs
      have lt : r < R := by simpa using hr
      have word := words i ⟨r,lt⟩
      simp only [List.getElem_ofFn]
      rw [←Nat.add_assoc]
      change decide (out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r) ≠ 0) = _
      rw [word,PurchaseStage.decode_flag width]
  calc
    sh.packedCount S k depth out = ∑ i : Key z d k, f i := by
      change (List.ofFn (fun r : Fin (count z d k*R) => decide (out (base+r.val)≠0))).count true = _
      rw [List.ofFn_mul (m:=count z d k) (n:=R) (fun r=>decide (out (base+r.val)≠0)),List.count_flatten,List.map_ofFn,List.sum_ofFn]
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (List.count true) (slab i)).trans (sh.decisions_count S π depth phase T kind frozen i)
    _ = ∑ p : StageAt z d × Fin (2*k), f (key p.1 p.2) := (finProdFinEquiv.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [f,stage_key]

/-- The true flags in the packed output count exactly the typed retained
chains for the actual signed inventory marks, including repeated geometric
tile numbers in different signed strata. -/
theorem packedCount_liveChains (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen out : Mem z d)
    (words : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
      out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)=
        MarkTape.encode (wordBits z d copies)
          ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp))) :
    sh.packedCount S k depth out =
      Fintype.card (LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k))) := by
  rw [sh.packedCount_eq S π depth phase T kind frozen out words, liveChain_card]
  apply Finset.sum_congr rfl
  intro t _
  let f := fun j : Fin (2*k) =>
    (advisedPurchases S π t depth (sh.marked phase T kind frozen (key t j))).1.length
  exact ((PurchaseMarks.signedDirection k).symm.sum_comp f).symm
end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
