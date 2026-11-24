import OAI.Computability.VPVNP.PairSimulationEndpointBits
import OAI.Computability.VPVNP.PairNodeArguments

/-! # Addresses and words gathered by a terminal vertex

The final slot count includes all sites. Its quotient by the number of sites
is the actual number of slots per site. Outgoing slots address the width and
prefix tables directly. Each incoming slot first selects its matched outgoing
slot from the inverse incidence table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- Addresses and sizes used to gather one final site's incident wire words from external
memory into the private argument block for its DFS root. -/
structure Layout where
  /-- Ordinal of the selected final site, used to locate its contiguous interval of incidence
  slots. -/
  vertex : ℕ
  /-- Number of final sites sharing the slot table. Dividing the total slot count by this value
  gives the scan length for one site. -/
  sites : ℕ
  /-- Total number of slots across all final sites in one direction of the incidence table. -/
  slots : ℕ
  /-- External base of the table giving the number of wire words for each outgoing slot. -/
  widthHead : ℕ
  /-- External base of the inverse incidence table mapping each incoming slot to the outgoing
  slot of its wire. -/
  incomingHead : ℕ
  /-- External base of the exclusive width-prefix table. Its entry for an outgoing slot is that
  wire's offset from the wire bank base. -/
  prefixHead : ℕ
  /-- External base address of the packed wire words addressed by the slot prefix table. -/
  wires : ℕ
  /-- Private argument bank base supplied in public word six. The gather adds the root's stride
  offset to obtain its packet destination. -/
  n : ℕ
  /-- Descriptor address of the selected site's DFS root, used as the index of its private
  argument block. -/
  root : ℕ
  /-- Number of private words between argument blocks for successive descriptor addresses,
  loaded from the geometry header at startup. -/
  stride : ℕ

namespace Layout

variable {w : ℕ}

/-- Slots scanned in each direction at one final site, computed by dividing the total slot
count by the site count. -/
def degree (L : Layout) := L.slots / L.sites
/-- Global slot index at offset `j` in the selected site's interval. At the site degree it
gives the exclusive loop bound. -/
def index (L : Layout) (j : ℕ) := L.vertex*L.degree+j
/-- Outgoing slot that owns the wire at a local endpoint. Outgoing slots use their global index
directly, while incoming slots read their partner from the inverse incidence table. -/
def edge (L : Layout) (mem : Memory w) (dir : Bool) (j : ℕ) :=
  if dir then (mem (L.incomingHead+L.index j)).val else L.index j

/-- Length in words of the selected endpoint field, read from the width table using its
outgoing slot index. -/
def width (L : Layout) (mem : Memory w) (dir : Bool) (j : ℕ) := (mem (L.widthHead+L.edge mem dir j)).val
/-- First external address of the endpoint field, obtained by adding its outgoing slot's
exclusive prefix to the wire bank base. -/
def start (L : Layout) (mem : Memory w) (dir : Bool) (j : ℕ) := L.wires+(mem (L.prefixHead+L.edge mem dir j)).val

/-- Contiguous wire words of one selected slot in increasing external address order, including
the empty list for a zero-width slot. -/
def field (L : Layout) (mem : Memory w) (dir : Bool) (j : ℕ) : List (Word w) :=
  List.ofFn fun i : Fin (L.width mem dir j) => mem (L.start mem dir j+i.val)

/-- Endpoint fields for all slots of the chosen site and direction in local slot order,
retaining their individual field boundaries. -/
def fields (L : Layout) (mem : Memory w) (dir : Bool) : List (List (Word w)) :=
  List.ofFn fun j : Fin L.degree => L.field mem dir j.val

/-- Root argument packet in copy order, with all outgoing fields concatenated before all
incoming fields. -/
def packet (L : Layout) (mem : Memory w) := (L.fields mem false).flatten ++ (L.fields mem true).flatten
/-- First private address of the root packet, equal to the argument bank base plus the root
descriptor address times the stride. -/
def dest (L : Layout) := L.n + L.root*L.stride

/-- Exactly the words whose addresses or endpoints must fit in a native
register. The source and destination cursors also hold the exclusive end. -/
structure Fits (L : Layout) (mem : Memory w) : Prop where
  sites : L.sites < 2^w
  slots : L.slots < 2^w
  lastIndex : L.index L.degree < 2^w
  inverseAddr : ∀ j < L.degree, L.incomingHead+L.index j < 2^w
  widthAddr : ∀ b j, j < L.degree → L.widthHead+L.edge mem b j < 2^w
  prefixAddr : ∀ b j, j < L.degree → L.prefixHead+L.edge mem b j < 2^w
  sourceEnd : ∀ b j, j < L.degree → L.start mem b j+L.width mem b j < 2^w
  destEnd : L.dest+(L.packet mem).length < 2^w

@[simp] theorem field_length (L : Layout) (mem : Memory w) (dir : Bool) (j : ℕ) :
    (L.field mem dir j).length = L.width mem dir j := by simp [field]

theorem packet_length (L : Layout) (mem : Memory w) : (L.packet mem).length =
    (∑ j : Fin L.degree, L.width mem false j) + ∑ j : Fin L.degree, L.width mem true j := by
  simp [packet,fields,List.length_flatten,List.sum_ofFn,Function.comp_def]

/-- Closed form of the private block written by the endpoint gather. -/
def placed (base : ℕ) (xs : List (Word w)) (old : Word w → Word w) (a : Word w) : Word w :=
  if base ≤ a.val then xs[a.val-base]?.getD (old a) else old a

theorem placed_inside {base : ℕ} (xs : List (Word w)) (old : Word w → Word w) (i : Fin xs.length)
    (h : base+xs.length ≤ 2^w) : placed base xs old (Fin.ofNat _ (base+i.val)) = xs[i.val] := by
  have hi : base+i.val < 2^w := (Nat.add_lt_add_left i.isLt _).trans_le h
  have hv : (Fin.ofNat (2^w) (base+i.val)).val = base+i.val := Nat.mod_eq_of_lt hi
  unfold placed
  rw [hv]
  simp

theorem placed_outside (base : ℕ) (xs : List (Word w)) (old : Word w → Word w) (a : Word w)
    (h : a.val < base ∨ base+xs.length ≤ a.val) : placed base xs old a = old a := by
  rcases h with h|h
  · simp [placed,Nat.not_le_of_lt h]
  · have hi : xs.length ≤ a.val-base := by omega
    simp [placed,List.getElem?_eq_none hi]

theorem placed_append (base : ℕ) (xs ys : List (Word w)) (old : Word w → Word w) :
    placed (base+xs.length) ys (placed base xs old) = placed base (xs++ys) old := by
  funext a
  by_cases h : base+xs.length ≤ a.val
  · have hb : base ≤ a.val := by omega
    have hi : xs.length ≤ a.val-base := by omega
    simp only [placed,h,hb,ite_true,List.getElem?_append_right hi,List.getElem?_eq_none hi,Option.getD_none]
    rw [Nat.sub_sub]
  · have hi : a.val-base < xs.length ∨ a.val < base := by omega
    rcases hi with hi|hi
    · simp [placed,h,List.getElem?_append_left hi]
    · simp [placed,h,Nat.not_le_of_lt hi]

theorem copy_field (L : Layout) (mem : Memory w) (dir : Bool) (j dst : ℕ) (old : Word w → Word w) :
    EndpointBits.copySlice mem (L.start mem dir j) dst (L.width mem dir j) old =
      placed dst (L.field mem dir j) old := by
  funext a
  by_cases h : dst ≤ a.val ∧ a.val < dst+L.width mem dir j
  · have hi : a.val-dst < L.width mem dir j := by omega
    simp [EndpointBits.copySlice,h,placed,field,hi]
  · have hi : a.val < dst ∨ dst+(L.field mem dir j).length ≤ a.val := by rw [field_length]; omega
    rw [placed_outside _ _ _ _ hi]; simp [EndpointBits.copySlice,h]

end Layout

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
