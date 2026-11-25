import OAI.Hierarchy.TaggedShorterReportAdvice

namespace OAI
/-! # The original fixed-port ranks and ROM cells survive the mask/ID publication -/

namespace Hierarchy.ProtocolRAMFrozenWidthFrame

open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM TaggedShorterReportAdvice
open scoped Fin.CommRing

variable {W N : ℕ}

/-- The physical bank is placed below the control board, and outside the one ignored sink. -/
structure Safe (b : Bank) (board sink : ℕ) : Prop where
  below : b.base+b.size ≤ board
  apart : sink < b.base ∨ b.base+b.size ≤ sink

theorem read (before after : Memory W) (board sink : ℕ)
    (frame : ∀ a,a < board→a≠sink→after a=before a) (b : Bank) (safe : Safe b board sink)
    (i : Word W) : b.read after i=b.read before i := by
  have sm : i.val%b.size < b.size := Nat.mod_lt _ (Nat.two_pow_pos b.bits)
  have low := safe.below
  have separate := safe.apart
  exact frame (b.base+i.val%b.size) (by omega) (by omega)

theorem dynamic (before after : Memory W) (board sink : ℕ)
    (frame : ∀ a,a < board→a≠sink→after a=before a) (rows : Fin N→ProtocolRAMEmit.Row)
    (width group rank left right : Bank) (cr : Fin N→ℕ) (lr : Bool→Fin N→ℕ)
    (old : Dynamic rows before width group rank left right cr lr)
    (w : Safe width board sink) (g : Safe group board sink) (c : Safe rank board sink)
    (l : Safe left board sink) (r : Safe right board sink) :
    Dynamic rows after width group rank left right cr lr where
  widthAt i := (read before after board sink frame width w _).trans (old.widthAt i)
  groupAt i := (read before after board sink frame group g _).trans (old.groupAt i)
  commonAt i := (read before after board sink frame rank c _).trans (old.commonAt i)
  leftAt i := (read before after board sink frame left l _).trans (old.leftAt i)
  rightAt i := (read before after board sink frame right r _).trans (old.rightAt i)

theorem table {groups D B M base w menu cap rom bits : ℕ} (before after : Memory W) (board sink : ℕ)
    (frame : ∀ a,a < board→a≠sink→after a=before a)
    (safe : ∀ j : Fin 13,Safe (bank rom bits j) board sink)
    (old : ∀ j : Fin 13,∀ x : ℕ,x<2^bits→(bank rom bits j).read before (x:Word W)=
      words groups D B M base w menu cap j x) :
    ∀ j : Fin 13,∀ x : ℕ,x<2^bits→(bank rom bits j).read after (x:Word W)=
      words groups D B M base w menu cap j x :=
  fun j x hx=>(read before after board sink frame _ (safe j) _).trans (old j x hx)


end Hierarchy.ProtocolRAMFrozenWidthFrame

end OAI
