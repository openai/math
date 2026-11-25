import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame

namespace OAI
/-! # Reopening the booted arrays at a later chronological purchase -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

noncomputable section
variable {z d k jobs size q n : ℕ}
variable {v : Fin jobs → Market z d k} {π : Equiv.Perm (Fin (2^z))} {raw mid : Tape z d}

/-- The only frozen inputs of this purchase are the shared CT columns and its own interval. -/
def reads (s : Market z d k) (x : ℕ) := x<heapEnd z d copies ∨ low s≤x ∧ x<high s

private theorem to_high (s : Market z d k) : s.shelf.firstBase≤high s := by
  unfold high Market.flags Shelf.flagsBase
  omega

private theorem pass_frame {w : ℕ} (p : Pass) (m : Memory w) (x : ℕ) (free : apart x p.out p.rows) :
    p.apply m x=m x := by
  have miss : ¬(p.out≤x ∧ x<p.out+p.rows) := by unfold apart at free; omega
  simp only [Pass.apply,image,fillSegment,ite_eq_right miss]

/-- Opening a genuine CT/price/sampler snapshot after any earlier events. The stock
banks are read from the new current memory when the signed purchase is evaluated. -/
theorem Receipt.market_ready (receipt : Receipt v π raw mid) (layout : Layout v size) (i : Fin jobs)
    (hd : 1≤d) (m : Tape z d)
    (same : ∀x,reads (v i) x → m x=mid x)
    (dimensions : ∀ j : Key z d k,Ready (v i).sampler (stage j) ((v i).shelf.cfg (v i).sampler (v i).depth j))
    (stock : ∀t : StageAt z d,∀j : Fin (2*k),((v i).shelf.stock t j).base+((v i).shelf.stock t j).size≤(v i).shelf.firstBase)
    (failFits : (v i).failures.pass.Fits (wordBits z d copies))
    (failRoom : (v i).failures.base+(v i).failures.rows≤(v i).shelf.firstBase)
    (failFree : ∀x,reads (v i) x → apart x (v i).failures.base (v i).failures.rows)
    (capacity : (v i).flags+(v i).rows<2^wordBits z d copies) :
    (v i).ready m := by
  let s := v i
  let out := s.failures.pass.apply m
  have frame (x : ℕ) (h : reads s x) : out x=mid x :=
    (pass_frame s.failures.pass m x (failFree x h)).trans (same x h)
  have geo := Shelf.geometry_of_frame π mid out receipt.geometry (fun x h=>frame x (.inl h))
  have table : PurchaseMarks.Table s.phase s.temperature k s.kind s.shelf.table out := by
    intro r
    let a := s.shelf.table.base+r.val%s.shelf.table.size
    have small : r.val%s.shelf.table.size<s.shelf.table.size := Nat.mod_lt _ (Nat.two_pow_pos _)
    have room := layout.threshold i
    change s.shelf.table.base+s.shelf.table.size ≤ s.shelf.firstBase at room
    have lt : a<s.shelf.firstBase := by dsimp [a]; omega
    change out a=_
    exact (frame a (.inr ⟨Nat.le_add_right ..,lt.trans_le (to_high s)⟩)).trans (receipt.table i r)
  have heap := (layout.afterHeap i).trans ((Nat.le_add_right ..).trans (layout.threshold i))
  refine ⟨failFits,failRoom,hd,capacity,π,price s raw,
    s.shelf.incoming s.sampler π s.depth s.phase s.temperature s.kind out dimensions geo table
      (layout.threshold i) stock heap,?_⟩
  intro j
  apply s.shelf.ready_of_frame s.sampler s.depth (price s raw) mid out j (receipt.rom i j)
  intro a lo hi
  have lower : low s≤a := (Nat.le_add_right ..).trans
    ((layout.threshold i).trans ((Nat.le_add_right ..).trans lo))
  exact frame a (.inr ⟨lower,
    hi.trans_le ((s.shelf.final_after s.sampler s.depth j).trans (Nat.le_add_right ..))⟩)

/-- Earlier purchases, their sparse commits and feed boundaries preserve the
current immutable rows when their actual writes avoid the indicated addresses. -/
theorem Receipt.ready_after_prefix (receipt : Receipt v π raw mid) (layout : Layout v size)
    (C : Chart (wordBits z d copies) q n) («prefix» : List Event) (a : Attempt) (i : Fin jobs)
    (hd : 1≤d) (ran : mounted C «prefix» mid)
    (earlier : ∀ x,reads (v i) x → ∀e∈«prefix»,outside C x e)
    (guardFree : ∀ x,reads (v i) x → x≠C.stopAt a)
    (dimensions : ∀ j : Key z d k,Ready (v i).sampler (stage j) ((v i).shelf.cfg (v i).sampler (v i).depth j))
    (stock : ∀t : StageAt z d,∀j : Fin (2*k),((v i).shelf.stock t j).base+((v i).shelf.stock t j).size≤(v i).shelf.firstBase)
    (failFits : (v i).failures.pass.Fits (wordBits z d copies))
    (failRoom : (v i).failures.base+(v i).failures.rows≤(v i).shelf.firstBase)
    (failFree : ∀x,reads (v i) x → apart x (v i).failures.base (v i).failures.rows)
    (capacity : (v i).flags+(v i).rows<2^wordBits z d copies) :
    (v i).ready ((guard C a).apply (run C «prefix» mid)) := by
  apply receipt.market_ready layout i hd _ _ dimensions stock failFits failRoom failFree capacity
  intro x region
  have nonoverlap : apart x (guard C a).out (guard C a).rows := by
    change x<C.stopAt a ∨ C.stopAt a+1≤x
    have ne := guardFree x region
    omega
  exact (pass_frame (guard C a) _ x nonoverlap).trans (run_outside C «prefix» mid x ran (earlier x region))

/-- A true input inventory cell outside the public tables is unchanged by CT subdivision. -/
theorem Receipt.initial_stock (receipt : Receipt v π raw mid) (b : Bank) (r : Word (wordBits z d copies))
    (start : heapEnd z d copies≤b.base) (before : ∀i,b.base+b.size≤low (v i)) :
    b.read mid r=b.read raw r := by
  let a := b.base+r.val%b.size
  have small : r.val%b.size<b.size := Nat.mod_lt _ (Nat.two_pow_pos _)
  have end_ : a<b.base+b.size := by dsimp [a]; omega
  exact receipt.kept a (start.trans (Nat.le_add_right ..)) (fun i hit=>
    (not_le_of_gt (end_.trans_le (before i))) hit.1)

/-- Read the original private selector/replay word in the actual machine state after a prefix.
Both post-batch updates and writes on either side of the immutable tape are covered. -/
theorem Receipt.word_after_prefix (receipt : Receipt v π raw mid)
    (C : Chart (wordBits z d copies) q n) («prefix» : List Event) (ran : mounted C «prefix» mid) (x : ℕ)
    (above : heapEnd z d copies≤x)
    (publicFree : ∀i,¬ ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i x)
    (untouched : ∀e∈«prefix»,outside C x e) : run C «prefix» mid x=raw x :=
  (run_outside C «prefix» mid x ran untouched).trans (receipt.kept x above publicFree)

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
