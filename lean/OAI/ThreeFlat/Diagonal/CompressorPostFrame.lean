import OAI.ThreeFlat.Diagonal.CompressorPostImage

namespace OAI
/-! # Preservation of the selected graph and widths through the site-directory sweeps -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
variable {w : ℕ}

def Pass.Avoids (p : Pass w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (low high : ℕ) : Prop :=
  match p with
  | .one s =>
    let a := (headerRead m current s.start).val
    let n := (headerRead m current s.length).val
    a+n<2^w ∧ (a+n≤low ∨ high≤a)
  | .seq a b =>
    a.Avoids current pub m low high ∧ b.Avoids current pub (a.execute current pub m).2 low high

theorem Pass.keeps (p : Pass w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    {low high : ℕ} (h : p.Avoids current pub m low high)
    (i : ℕ) (left : low≤ i) (right : i<high) : (p.execute current pub m).2 i=m i := by
  induction p generalizing m with
  | one s =>
    let a := headerRead m current s.start
    let n := (headerRead m current s.length).val
    have sep : a.val+n≤low ∨ high≤a.val := h.2
    have out : i<a.val ∨ a.val+n≤ i := by rcases sep with h|h <;> omega
    exact sweep_frame (fun j alt=>s.row.eval pub alt (fun _=>j)) n a m h.1 i out
  | seq a b ia ib => exact (ib _ h.2).trans (ia _ h.1)

theorem descriptors_preserve {B L : Type*} {d N Z : ℕ} (G : LiftedSlots B d L)
    (b : B ≃ Fin N) (lane : L ≃ Fin Z) (C : SlotImage.Columns) (width : SlotImage.Edge B L d → ℕ)
    (S : Graph.Stage) (K kind : ℕ) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (ready : SlotImage.Stored G b lane C (fun i=>(((post current S).execute current pub m).2 i).val) width)
    (graph : ((NodeRecipe.descriptors S K kind).install current).Avoids current pub
      ((post current S).execute current pub m).2 C.graph (C.graph+6*C.rows))
    (widths : ((NodeRecipe.descriptors S K kind).install current).Avoids current pub
      ((post current S).execute current pub m).2 C.widths (C.widths+N*d*Z)) :
    SlotImage.Stored G b lane C (fun i=>((((NodeRecipe.after S K kind).install current).execute current pub m).2 i).val)
      width := by
  apply ready.frame
  · exact fun i lo hi=>congrArg Fin.val (Pass.keeps _ _ _ _ graph i lo hi)
  · exact fun i lo hi=>congrArg Fin.val (Pass.keeps _ _ _ _ widths i lo hi)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
