import OAI.Computability.VPVNP.CompressorRecordsABScan
import OAI.Computability.VPVNP.CompressorRecordsBundleLists

/-!
# AB rows in the mathematical motif numbering

The bundle-total column is indexed by the assigned outgoing port. The native
piece scan constructs widths and starts in the same order as the AB demands
at their two packed endpoints, for every absolute lane and every parallel port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ABWidths

open Compression Compression.PackingData BurstRAM PrimedStackRAM

variable {V H T L : Type} {d c n w : ℕ}
variable [Fintype V] [Fintype H] [Fintype T] [Fintype L]
variable [DecidableEq V] [DecidableEq T] [DecidableEq L]
variable [AddCommGroup H] [AddCommGroup T] [AddCommGroup L]
variable (P : PackingData V H T L d c) (number : P.BundleNumbering) (site : Site V T L ≃ Fin n)
variable (old : Arc V H T L d c → ℕ)

private theorem width_in_fiber (b : Site V T L × Fin d) (z : P.MotifFiber b) :
    P.abWidth number old z.1 = splitWidth (P.bundleWidth old b) (pieceCount d c) (number b z) := by
  obtain ⟨m,h⟩ := z
  subst b
  rfl

private theorem offset_in_fiber (b : Site V T L × Fin d) (z : P.MotifFiber b) :
    pieceStart (P.bundleWidth old b) (pieceCount d c) (number b z).val =
      fieldStart (number b) (fun m ↦ P.abWidth number old m.val) z := by
  rw [prefix_sum, fieldStart, fieldStart]
  apply Finset.sum_congr rfl
  intro i _
  rw [width_in_fiber P number old, Equiv.apply_symm_apply]
  rfl

/-- Memory representation of all two-ended AB fields, with natural addresses and
the stride used by the term-row and kernel-slice readers. -/
structure ABColumns (p : Fin 5 → Word w) (m : Memory w) : Prop where
  widths : ∀ b : Site V T L × Fin d, ∀ j : Fin (pieceCount d c),
    (m ((p 3).val+(BundleLists.portIndex site b).val*(p 1).val+j.val)).val =
      P.abWidth number old ((number b).symm j).val
  starts : ∀ b : Site V T L × Fin d, ∀ j : Fin (pieceCount d c),
    (m ((p 4).val+(BundleLists.portIndex site b).val*(p 1).val+j.val)).val =
      fieldStart (number b) (fun z ↦ P.abWidth number old z.val) ((number b).symm j)

/-- All AB widths and offsets are computed in one native segment. -/
theorem graph_run (p : Fin 5 → Word w) (m : Memory w) (layout : Layout p (n*d))
    (count : (p 0).val = pieceCount d c)
    (totals : ∀ b : Site V T L × Fin d,
      (m ((p 2).val+(BundleLists.portIndex site b).val)).val = P.bundleWidth old b) :
    let N := (n*d)*pieceCount d c
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 30 (some (Fin.ofNat _ 0)) m (List.replicate N []) = some rs ∧
      ABColumns P number site old p (after m (eventLog rs)) ∧
      Filled p m (after m (eventLog rs)) N ∧ rs.length = N ∧
      RAMBuckets.cost Report.probes rs = 4*N := by
  intro N M
  obtain ⟨rs,hr,hf,_,hn,_,hc⟩ := run p (n*d) m layout.regions
  have size : (n*d)*(p 0).val = N := congrArg ((n*d)*·) count
  refine ⟨rs,size ▸ hr,⟨?_,?_⟩,size ▸ hf,size ▸ hn,size ▸ hc⟩
  all_goals
    intro b j
    let u := BundleLists.portIndex site b
    let s := j.cast count.symm
    have hs : s.val < (p 1).val := s.isLt.trans_le layout.stride
    have hidx : u.val*(p 1).val+s.val < (n*d)*(p 1).val := by
      have h := Nat.mul_le_mul_right (p 1).val u.isLt
      rw [Nat.succ_mul] at h; omega
    have idx (t : Fin 2) : (p (t.natAdd 3) + Fin.ofNat (2^w) (u.val*(p 1).val+s.val)).val =
        (p (t.natAdd 3)).val+u.val*(p 1).val+j.val := by
      have h := layout.outFit t
      have hj : j.val = s.val := rfl
      rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega),Nat.add_assoc,hj]
    have htaddr : (p 2 + Fin.ofNat (2^w) u.val).val = (p 2).val+u.val := by
      have h := layout.totalFit; have hu := u.isLt
      rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
    obtain ⟨hwidth,hstart⟩ := hf.piece layout.regions u s
    change (after m (eventLog rs) ((p (Fin.natAdd 3 (0 : Fin 2))+Fin.ofNat _ (u.val*(p 1).val+s.val)).val)).val =
      splitWidth (m (p 2+Fin.ofNat _ u.val).val).val (p 0).val s at hwidth
    change (after m (eventLog rs) ((p (Fin.natAdd 3 (1 : Fin 2))+Fin.ofNat _ (u.val*(p 1).val+s.val)).val)).val =
      pieceStart (m (p 2+Fin.ofNat _ u.val).val).val (p 0).val s.val at hstart
    rw [idx 0,htaddr,totals] at hwidth
    rw [idx 1,htaddr,totals] at hstart
    change _ = pieceStart (P.bundleWidth old b) (p 0).val j.val at hstart
    rw [count] at hstart
  · apply hwidth.trans
    rw [width_in_fiber,Equiv.apply_symm_apply]
    exact congrArg (fun q ↦ if j.val < P.bundleWidth old b % q then P.bundleWidth old b / q + 1
      else P.bundleWidth old b / q) count
  · apply hstart.trans
    simpa only [Equiv.apply_symm_apply] using offset_in_fiber P number old b ((number b).symm j)

end CompressorRecords.ABWidths

end VPVNP
end Computability
end OAI
