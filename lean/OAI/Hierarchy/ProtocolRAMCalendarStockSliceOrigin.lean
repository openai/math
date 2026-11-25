import OAI.Hierarchy.ProtocolRAMCalendarStockOrigin

namespace OAI
/-! # Pointwise origin of the actual joint reserve-feed table -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.JointHeader
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped Classical Fin.CommRing
variable {jobs phases z d N k : ℕ}

theorem boot_slice {size : ℕ} (b : Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest fixture : Boot.Tape z d)
    (markets : Fin jobs→Market z d k) (layout : Boot.Layout markets size)
    (hd : 1≤d) (first : 2^z≤b.initial) (heap : heapEnd z d copies≤b.initial)
    (fits : stop b z N k phases≤ size) (before : ∀i,stop b z N k phases≤Boot.low (markets i)) :
    let table:=FeedROM.sliceBank b.initial (GlobalTests.rows z N k) b.steps b.cap b.width
    let mem:=Boot.booted markets size (words b z d N k phase π stock rest)
    ∀x,table.base≤x→x<table.base+b.steps*(b.cap*b.width+1)→
      mem x=feedAdvice table b.steps (b.cap*b.width+1) fixture x := by
  intro table mem x lo hi
  have enough : b.steps*(b.cap*b.width+1)≤table.size := sliceROM_size _ _ _
  have below : x<(scores b z N k).base := by
    change x<table.base+table.size+(half b z N k).size
    omega
  have low : b.initial≤table.base := Nat.le_add_right ..
  have kept:=low_origin b phase π stock rest markets layout hd first fits before x
    (heap.trans (low.trans lo)) below
  have word:=FeedROM.slice_cell b.initial (GlobalTests.rows z N k) b.steps b.cap b.width
    (inventory b z N k stock (Boot.permutationWords π rest)) x hi
  exact kept.trans (word.trans (by
    change feedAdvice table b.steps (b.cap*b.width+1) _ x=feedAdvice table b.steps (b.cap*b.width+1) fixture x
    simp only [feedAdvice,ThreeFlat.RAM.fillSegment,ite_eq_left (And.intro lo hi)]))

end Hierarchy.ProtocolRAM.Calendar.JointHeader
end

end OAI
