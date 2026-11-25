import OAI.Computability.BorderVNP.TransmissionPins
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # The public layout and register invariant for §11's secondary pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

/-- Physical dimensions and addresses used in the pin loops. -/
structure Layout where
  /-- Calling team number. -/
  team : ℕ
  /-- Number of teams in the layout. -/
  teams : ℕ
  /-- Number of processors per team. -/
  processors : ℕ
  /-- Bit width of a literal field. -/
  literal : ℕ
  /-- Bit width of a link field. -/
  link : ℕ
  /-- Number of genuine index bits. -/
  width : ℕ
  /-- Base of the substituted array. -/
  ibase : ℕ
  /-- Base of the copied live index. -/
  hbase : ℕ
  /-- Base of the public reference index. -/
  starbase : ℕ

/-- Distance to the second literal field within a processor. -/
def Layout.offset (L : Layout) : ℕ := L.literal + (L.teams - 1) * L.link

/-- Physical distance between successive processors. -/
def Layout.stride (L : Layout) : ℕ := L.offset + L.literal

/-- Total number of flat secondary pin positions. -/
def Layout.count (L : Layout) : ℕ := L.processors * L.literal

/-- Positions at which an independent substitution bit is chosen. -/
def Layout.active (L : Layout) (x : ℕ) : Prop := L.team = 0 ∧ x < L.width

/-- The ordinary public frame fields read by the initialization code. -/
structure Frame (L : Layout) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Field zero holds the caller's team number. -/
  team : frameField pub mem 0 = L.team
  /-- Field one holds the number of teams. -/
  teams : frameField pub mem 1 = L.teams
  /-- Field two holds the processor count. -/
  processors : frameField pub mem 2 = L.processors
  /-- Field three holds the literal width. -/
  literal : frameField pub mem 3 = L.literal
  /-- Field four holds the link width. -/
  link : frameField pub mem 4 = L.link
  /-- Field 21 holds the substitution array base. -/
  ibase : frameField pub mem 21 = L.ibase
  /-- Field 22 holds the live-copy base. -/
  hbase : frameField pub mem 22 = L.hbase
  /-- Field 23 holds the true index width. -/
  width : frameField pub mem 23 = L.width
  /-- Field 24 holds the reference index base. -/
  starbase : frameField pub mem 24 = L.starbase

/-- Numeric values of the persistent registers at flat position `x`. -/
structure Ready {w : ℕ} (L : Layout) (x : ℕ) (s : Bank w) : Prop where
  /-- Caller team in register zero. -/
  team : readings s 0 = L.team
  /-- Literal one in register one. -/
  one : readings s 1 = 1
  /-- Literal zero in register two. -/
  zero : readings s 2 = 0
  /-- Literal width in register three. -/
  literal : readings s 3 = L.literal
  /-- Processor stride in register four. -/
  stride : readings s 4 = L.stride
  /-- Second-field offset in register five. -/
  offset : readings s 5 = L.offset
  /-- Current flat cursor in register six. -/
  cursor : readings s 6 = x
  /-- Total flat position count in register seven. -/
  count : readings s 7 = L.count
  /-- Genuine index width in register eight. -/
  width : readings s 8 = L.width
  /-- Substituted-array base in register nine. -/
  ibase : readings s 9 = L.ibase
  /-- Live-copy base in register ten. -/
  hbase : readings s 10 = L.hbase
  /-- Public reference base in register eleven. -/
  starbase : readings s 11 = L.starbase

/-- Preservation of the twelve persistent registers preserves the invariant. -/
theorem Ready.congr {w : ℕ} {L : Layout} {x : ℕ} {s t : Bank w} (h : Ready L x s)
    (agree : ∀ i : Reg, i.val < 12 → readings t i = readings s i) : Ready L x t :=
  ⟨(agree 0 (by decide)).trans h.team, (agree 1 (by decide)).trans h.one,
   (agree 2 (by decide)).trans h.zero, (agree 3 (by decide)).trans h.literal,
   (agree 4 (by decide)).trans h.stride, (agree 5 (by decide)).trans h.offset,
   (agree 6 (by decide)).trans h.cursor, (agree 7 (by decide)).trans h.count,
   (agree 8 (by decide)).trans h.width, (agree 9 (by decide)).trans h.ibase,
   (agree 10 (by decide)).trans h.hbase, (agree 11 (by decide)).trans h.starbase⟩

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
