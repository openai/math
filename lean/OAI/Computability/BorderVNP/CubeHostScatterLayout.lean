import OAI.Computability.BorderVNP.CubeDirectedIntervalPrepare
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Actual public pointers for restoring each cell's external cable inputs

The directed-bin prefix and the canonical pair metadata determine the source.
The supplied two-sided physical slot directory determines the destination.
A team touches a bit only at a crossing endpoint of a cell that it owns.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Physical bases and sizes of the inputs to the final host-cable scatter. -/
structure Layout where
  /-- Common public frame. -/
  frame : ℕ
  /-- Three-word cable directory. -/
  cables : ℕ
  /-- Number of cable rows. -/
  count : ℕ
  /-- Per-cell chosen label. -/
  labels : ℕ
  /-- Number of product-alphabet labels. -/
  alphabet : ℕ
  /-- Within-bin starting ordinal per cable. -/
  ordinals : ℕ
  /-- Two words per cell, its owner and external bit-bank base. -/
  cells : ℕ
  /-- Two relative external offsets per cable, in source/destination order. -/
  relative : ℕ
  /-- Kind, first packet and antipodal vertex number per ordered label pair. -/
  pairs : ℕ
  /-- Base of the padded singleton bit array. -/
  singles : ℕ
  /-- Base of the packet bit banks. -/
  packets : ℕ
  /-- Number of blocks per directed pair. -/
  blocks : ℕ
  /-- Fixed block width. -/
  bc : ℕ
  /-- Uniform packet bank width. -/
  bankWidth : ℕ
  /-- Number of selector bits before the demand-end slots. -/
  selectorWidth : ℕ
  /-- Executing physical team. -/
  team : ℕ

/-- Persistent native registers occupied by the public configuration. -/
def Layout.regValue (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => l.cables | 5 => l.count | 6 => l.labels
  | 7 => l.alphabet | 8 => l.ordinals | 9 => l.cells | 10 => l.relative | 11 => l.pairs | 12 => l.singles
  | 24 => l.packets | 25 => l.blocks | 26 => l.bc | 27 => l.bankWidth | 28 => l.selectorWidth | 29 => l.team
  | _ => 0

/-- Configuration words already loaded from the public frame. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop :=
  ∀ j : Reg, (j.val ≤ 12 ∨ 24 ≤ j.val ∧ j.val ≤ 29) → z.reg j = l.regValue j.val

/-- Endpoint cell in the real cable directory. -/
def Layout.cell (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) := m (l.cables+3*i+side.toNat)

/-- Width of the real cable. -/
def Layout.width (l : Layout) (m : ℕ → ℕ) (i : ℕ) := m (l.cables+3*i+2)

/-- The directed ordered-label key read from the two chosen labels. -/
def Layout.key (l : Layout) (m : ℕ → ℕ) (i : ℕ) :=
  m (l.labels+l.cell m i false)*l.alphabet+m (l.labels+l.cell m i true)

/-- The corresponding endpoint's physical owner. -/
def Layout.owner (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) := m (l.cells+2*l.cell m i side)

/-- Test before entering the bit loop, retaining arbitrary padding rows and internal cell cables. -/
def Layout.Owned (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) : Prop :=
  l.width m i ≠ 0 ∧ l.cell m i false ≠ l.cell m i true ∧ l.owner m i side = l.team

instance (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) : Decidable (l.Owned m i side) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The absolute start of this cable's exterior interval in its endpoint's cell. -/
def Layout.dest (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) :=
  m (l.cells+2*l.cell m i side+1) + m (l.relative+2*i+side.toNat)

/-- Read the appropriate singleton slot or packet's antipodal demand end, using the
within-pair ordinal, packet block division and the two public endpoint orientations. -/
def Layout.source (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) (j : ℕ) :=
  let k := l.key m i
  let a := l.pairs+3*k
  let ord := m (l.ordinals+i)+j
  if m a = 0 then l.singles + k*(l.blocks*l.bc) + ord else
    l.packets+(m (a+1)+ord/l.bc)*l.bankWidth+l.selectorWidth+
      (2*m (a+2)+side.toNat)*l.bc+ord%l.bc

/-- Header and metadata reads needed before the bit loop. -/
def Layout.rowReads (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) : List ℕ :=
  let c := l.cell m i side
  let a := l.pairs+3*l.key m i
  [l.cables+3*i,l.cables+3*i+1,l.cables+3*i+2,l.cells+2*c,l.cells+2*c+1,
   l.relative+2*i+side.toNat,l.labels+l.cell m i false,l.labels+l.cell m i true,
   l.ordinals+i,a,a+1,a+2]

/-- Input metadata and source-bit addresses whose initial values are retained throughout the pass. -/
def Layout.Input (l : Layout) (m : ℕ → ℕ) (a : ℕ) : Prop :=
  ∃ i < l.count, ∃ side : Bool, a ∈ l.rowReads m i side ∨
    (l.Owned m i side ∧ ∃ j < l.width m i, a = l.source m i side j)

/-- Memory agrees with the input on all future directory and bit-source reads. -/
def Layout.Frozen (l : Layout) (before mem : ℕ → ℕ) : Prop :=
  ∀ a, l.Input before a → mem a = before a

/-- One endpoint pass copies only its actual contiguous interval. -/
def Layout.copyEnd (l : Layout) (before mem : ℕ → ℕ) (i : ℕ) (side : Bool) (a : ℕ) :=
  if l.Owned before i side ∧ l.dest before i side ≤ a ∧ a < l.dest before i side+l.width before i
  then before (l.source before i side (a-l.dest before i side)) else mem a

/-- Entire memory after scanning the first `i` cables and visiting both endpoints. -/
def Layout.prefix (l : Layout) (before : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => before
  | i+1 => l.copyEnd before (l.copyEnd before (l.prefix before i) i false) i true

/-- Count of physical bit copies at an endpoint, including zero copies for nonowned or internal cables. -/
def Layout.bits (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) :=
  if l.Owned m i side then l.width m i else 0

/-- Total bit work is the incident width of crossing endpoints assigned to this team. -/
def Layout.incident (l : Layout) (m : ℕ → ℕ) :=
  ∑ i ∈ Finset.range l.count, (l.bits m i false + l.bits m i true)

/-- Finite word and separation conditions for the native cable pass. The source bits
and dynamic metadata avoid the written external interval of every owned endpoint. -/
structure Layout.Fits (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Positive block and packet width allow the native division and products. -/
  positive : 0 < l.bc ∧ 0 < l.bankWidth
  /-- The loop's terminal counter fits. -/
  countFit : l.count < 2^w
  /-- The three-word directory fits. -/
  directory : l.cables+3*l.count ≤ 2^w
  /-- The selected owner's table is readable even for nonowned live endpoints. -/
  ownerFit : ∀ i < l.count, ∀ side, l.width m i ≠ 0 → l.cell m i false ≠ l.cell m i true →
    l.cells+2*l.cell m i side < 2^w
  /-- Metadata reads of owned endpoints fit. -/
  rowFit : ∀ i < l.count, ∀ side, l.Owned m i side → ∀ a ∈ l.rowReads m i side, a < 2^w
  /-- Absolute source address of every copied bit fits. -/
  sourceFit : ∀ i < l.count, ∀ side, l.Owned m i side → ∀ j < l.width m i, l.source m i side j < 2^w
  /-- Padded bin stride and the starting-ordinal counter fit even at zero key. -/
  stride : l.blocks*l.bc < 2^w
  /-- Starting ordinal plus the occupied width stays in the padded interval. -/
  ordFit : ∀ i < l.count, ∀ side, l.Owned m i side → m (l.ordinals+i)+l.width m i ≤ l.blocks*l.bc
  /-- Each written interval is addressable. -/
  destFit : ∀ i < l.count, ∀ side, l.Owned m i side → l.dest m i side+l.width m i ≤ 2^w
  /-- All metadata and source bits lie outside every actual write interval. -/
  disjoint : ∀ i < l.count, ∀ side, l.Owned m i side → ∀ a, l.Input m a →
    a < l.dest m i side ∨ l.dest m i side+l.width m i ≤ a

/-- One copied destination interval preserves every immutable metadata and source word. -/
theorem Layout.Frozen.copyEnd {l : Layout} {w i : ℕ} {before mem : ℕ → ℕ} (h : l.Frozen before mem)
    (fit : l.Fits w before) (hi : i < l.count) (side : Bool) : l.Frozen before (l.copyEnd before mem i side) := by
  intro a ha
  by_cases ho : l.Owned before i side
  · have hx := fit.disjoint i hi side ho a ha
    simp only [Layout.copyEnd,ho,true_and]
    rw [ite_eq_right (by omega)]
    exact h a ha
  · simp only [Layout.copyEnd,ho,false_and,ite_false]
    exact h a ha

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
