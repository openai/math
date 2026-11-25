import OAI.ThreeFlat.Diagonal.RefreshChoiceImage

namespace OAI
/-! # Exact header scans indexed by a finite physical coordinate chart -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.DescriptorScan RAM.DescriptorExpr CompressorPacking.Native
open scoped Fin.CommRing

variable {W n : ℕ} {A : Type} (current : Word W) (m : Memory W)
set_option quotPrecheck false
local notation "N" => fun i=>(m i).val

theorem scan_table (e : A ≃ Fin n) (word : A → Word W) (f : Term W 0 1)
    (start size base : ℕ) (header : (m current.val).val+max start size<2^W)
    (ptr : info N current start=base) (len : info N current size=n) (cap : base+n<2^W)
    (rows : ∀ a (reg : Word W) (m' : Memory W),reg.val=base+(e a).val →
      agreesOutside base (base+n) m' m → f.eval Fin.elim0 m' (fun _=>reg)=word a) :
    (Pipeline.scan current start size f).run m=fillSegment base n (tableWord e base word) m := by
  have low := (header_val current m start (by omega)).trans ptr
  have count := (header_val current m size (by omega)).trans len
  let row := fun a m' => f.eval Fin.elim0 m' (fun _=>a)
  change sweep row _ _ m=_
  rw [count]
  calc
    _ = fillSegment (headerWord m current start).val n (tableWord e base word) m := by
      apply sweep_segment row base (base+n) m _ _ _ _ m low.ge (by omega) cap (fun _ _=>rfl)
      intro x lower upper m' frame
      let i : Fin n := ⟨x.val-base,by omega⟩
      let a := e.symm i
      have key : (e a).val=x.val-base := congrArg Fin.val (e.apply_symm_apply i)
      have loc : x.val=base+(e a).val := by omega
      exact (rows a x m' loc frame).trans (by rw [loc,tableWord_at])
    _ = _ := by rw [low]

theorem scan_read (e : A ≃ Fin n) (word : A → Word W) (lo : ℕ) (a : A) :
    fillSegment lo n (tableWord e lo word) m (lo+(e a).val)=word a := by
  have bound := (e a).isLt
  simp [fillSegment,tableWord_at,bound]

theorem segment_other (lo n : ℕ) (word : ℕ → Word W) (i : ℕ) (apart : i<lo ∨ lo+n≤ i) :
    fillSegment lo n word m i=m i := by
  simp only [fillSegment,ite_eq_right (by omega : ¬ (lo≤ i ∧ i<lo+n))]

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
