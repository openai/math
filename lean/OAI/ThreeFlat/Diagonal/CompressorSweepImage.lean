import OAI.ThreeFlat.Diagonal.CompressorStageBlocks
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # Materializing the physical word files produced by a shrinking sweep -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan
open scoped Fin.NatCast

variable {w : ℕ}
theorem sweep_image (f : Word w → Memory w → Word w) (lo hi : ℕ) (m₀ : Memory w)
    (file : ℕ → Word w) (fit : hi<2^w)
    (correct : ∀ (a : Word w) m, lo≤a.val → a.val<hi → agreesOutside lo hi m m₀ → f a m=file a.val)
    (n : ℕ) (a : Word w) (m : Memory w) (lower : lo≤a.val) (upper : a.val+n≤hi)
    (frame : agreesOutside lo hi m m₀) :
    sweep f n a m = fillSegment a.val n file m := by
  induction n generalizing a m with
  | zero => simp [sweep]
  | succ n ih =>
    have inside : a.val<hi := by omega
    have next : (a+1).val=a.val+1 := Fin.val_add_one_of_lt' (by omega)
    have safe : agreesOutside lo hi (writeMemory m a (file a.val)) m₀ := by
      intro i h
      have ne : i≠a.val := by rcases h with h|h <;> omega
      simpa [writeMemory,ne] using frame i h
    rw [sweep,correct a m lower inside frame,fillSegment_succ]
    rw [ih (a+1) _ (by omega) (by omega) safe,next]

/-- One installed span has the requested row file and preserves all other
words. This statement uses the same executing pass as the linked RAM bank. -/
theorem one_image (p : Span w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (lo len : ℕ) (file : ℕ → Word w) (fit : lo+len<2^w)
    (low : (headerRead m current p.start).val=lo)
    (count : (headerRead m current p.length).val=len)
    (correct : ∀ (a : Word w) alt, lo≤a.val → a.val<lo+len → agreesOutside lo (lo+len) alt m →
      p.row.eval pub alt (fun _=>a)=file a.val) :
    ((Pass.one p).execute current pub m).2=fillSegment lo len file m := by
  change sweep _ _ _ _=_
  rw [count]
  have run := sweep_image (fun a alt=>p.row.eval pub alt (fun _=>a)) lo (lo+len) m
    file fit correct len (headerRead m current p.start) m
    (by omega) (by omega) (fun _ _=>rfl)
  simpa only [low] using run

theorem sweep_frame (f : Word w → Memory w → Word w) (n : ℕ) (a : Word w) (m : Memory w)
    (bound : a.val+n<2^w) : agreesOutside a.val (a.val+n) (sweep f n a m) m := by
  induction n generalizing a m with
  | zero => exact fun _ _=>rfl
  | succ n ih =>
    have next : (a+1).val=a.val+1 := Fin.val_add_one_of_lt' (by omega)
    intro i side
    have far : i<(a+1).val ∨ (a+1).val+n≤ i := by rcases side with h|h <;> omega
    have ne : i≠a.val := by rcases side with h|h <;> omega
    have h := ih (a+1) (writeMemory m a (f a m)) (by omega) i far
    simpa only [sweep,writeMemory,ite_eq_right ne] using h

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
