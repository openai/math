import OAI.Computability.BorderVNP.CubeScatterCableAddress
import OAI.Computability.BorderVNP.CubeCableHostScatter

/-! # Runtime header and arithmetic layout for the physical padding check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM HostScatter

/-- Public quantities cached once, prior to traversing the directed label pairs. -/
structure Layout where
  /-- Address of the public RAM frame. -/
  frame : ℕ
  /-- Number of symbols at the selected product axis. -/
  groups : ℕ
  /-- Number of whole product labels. -/
  labels : ℕ
  /-- Positional radix power at the selected axis. -/
  place : ℕ
  /-- Base of the symbol-to-team owner table. -/
  owners : ℕ
  /-- Base of the actual occupied-width table for directed bins. -/
  widths : ℕ
  /-- Base of the three-word kind, packet and vertex directory. -/
  triples : ℕ
  /-- Base of the resident singleton bit bank. -/
  singles : ℕ
  /-- Base of the resident packet bit banks. -/
  packets : ℕ
  /-- Number of packet-sized blocks allocated per bin. -/
  blocks : ℕ
  /-- Width of one reserved block. -/
  bc : ℕ
  /-- Distance between successive packet banks. -/
  bankWidth : ℕ
  /-- Selector prefix before the first demand lane. -/
  selectorWidth : ℕ
  /-- Numeric identifier of the executing team. -/
  team : ℕ

/-- Cache contents decoded from the published frame and declaration. -/
def Layout.fromFrame (frame : ℕ) (m : ℕ → ℕ) : Layout :=
  let H := m (frame+63)
  ⟨frame,m (frame+59),m (frame+56),m (m (frame+62)+m (H+5)),m (frame+77),m (frame+57),m (frame+91),
    m (frame+88),m (H+8),m (H+7),m (frame+61),m (frame+93),m (frame+94),m frame⟩

/-- Number of ordered label pairs. -/
def Layout.count (l : Layout) := l.labels*l.labels

/-- Size of the reserved directed bin. -/
def Layout.stride (l : Layout) := l.blocks*l.bc

/-- Input and output owner read the source and target digits respectively. -/
def Layout.label (l : Layout) (key : ℕ) (side : Bool) := if side then key%l.labels else key/l.labels

/-- Physical address of the group-owner lookup. -/
def Layout.ownerAt (l : Layout) (key : ℕ) (side : Bool) := l.owners+(l.label key side/l.place)%l.groups

/-- Physical group assignment of the selected endpoint. -/
def Layout.owner (l : Layout) (m : ℕ → ℕ) (key : ℕ) (side : Bool) := m (l.ownerAt key side)

/-- The cached physical host address routine is applied from the occupied width to
the end of this bin. Its destination is unused by this read-only verification. -/
def Layout.fields (l : Layout) (m : ℕ → ℕ) (key : ℕ) (side : Bool) : BitFields :=
  let used := m (l.widths+key)
  let metadata := l.triples+3*key
  ⟨l.stride-used,key,used,m metadata,m (metadata+1),m (metadata+2),side.toNat,0,
    l.singles,l.packets,l.blocks,l.bc,l.bankWidth,l.selectorWidth⟩

/-- Shared native register cache that survives both endpoint checks and cursor updates. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop :=
  z.reg 0=0 ∧ z.reg 1=1 ∧ z.reg 2=2 ∧ z.reg 3=3 ∧ z.reg 4=l.groups ∧ z.reg 5=l.count ∧
  z.reg 6=l.place ∧ z.reg 7=l.labels ∧ z.reg 8=l.owners ∧ z.reg 9=l.widths ∧ z.reg 11=l.triples ∧
  z.reg 12=l.singles ∧ z.reg 24=l.packets ∧ z.reg 25=l.blocks ∧ z.reg 26=l.bc ∧ z.reg 27=l.bankWidth ∧
  z.reg 28=l.selectorWidth ∧ z.reg 29=l.team

/-- Word bounds on the genuinely executed directory arithmetic and physical bit reads. -/
structure Layout.Fits (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop where
  groups : 0 < l.groups
  place : 0 < l.place
  labels : 0 < l.labels
  count : l.count < 2^w
  stride : l.stride < 2^w
  owner : ∀ key < l.count, ∀ side, l.ownerAt key side < 2^w
  widthAddress : ∀ key < l.count, l.widths+key < 2^w
  tripleAddress : ∀ key < l.count, l.triples+3*key+2 < 2^w
  used : ∀ key < l.count, m (l.widths+key) ≤ l.stride
  bits : ∀ key < l.count, ∀ side, l.owner m key side = l.team → (l.fields m key side).Fits w

/-- All owned endpoints pass the actual zero tests on every unused physical slot. -/
def Layout.Valid (l : Layout) (m : ℕ → ℕ) : Prop :=
  ∀ key < l.count, ∀ side, l.owner m key side = l.team →
    ∀ j < (l.fields m key side).width, m ((l.fields m key side).source j) = 0

/-- Number of physical padding slots actually assigned to this team and endpoint. -/
def Layout.assigned (l : Layout) (m : ℕ → ℕ) (key : ℕ) (side : Bool) :=
  if l.owner m key side = l.team then (l.fields m key side).width else 0

end Cube.Padding

end BorderVNP
end Computability
end OAI
