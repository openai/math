import OAI.Computability.BorderVNP.CubePhysicalRoutedTallies
import OAI.Computability.BorderVNP.CellDirectoryObservationLedger
import OAI.Computability.BorderVNP.DiagonalTallyRAMEvaluation

/-! # Native sparse operand subtotals on one fully assigned physical path

The unary operands read the reported use bits. A merged private cell checks its externally
supplied count words against its observed table IDs. Every routed cube vertex contributes
one ID from the actual cube table. Finite orderings retain the physical row order while
counting every routed source once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open Crossing Diagonal Diagonal.CellEntries DiagonalTallyMaterialize DiagonalTallyScatter
open scoped BigOperators Classical

/-- One reported unary bit and its three native address sources. -/
structure UseRead where
  /-- Address of the parameter coordinate. -/
  parameterAddr : ℕ
  /-- Address of the binary place. -/
  placeAddr : ℕ
  /-- Pointer to the bit-address list. -/
  referenceAddr : ℕ
  /-- Address of the delivered and checked use bit. -/
  bitAddr : ℕ
  /-- Value read at the checked use-bit address. -/
  bit : Bool

/-- Runtime addresses for the one-unit operand of a routed packet vertex. -/
structure PacketRead where
  /-- Address filled by the packet table lookup. -/
  idAddr : ℕ
  /-- Address of the constant zero word. -/
  zeroAddr : ℕ
  /-- Address of the reference to the constant-one bit. -/
  referenceAddr : ℕ
  /-- Address of the constant-one bit. -/
  oneAddr : ℕ

/-- A passing sparse cell and its ordered original-site observations. The bank, directory,
reported word addresses and per-site observation lists refer to this one private assignment. -/
structure CellRead (Site : Type*) (U : ℕ) where
  /-- Number of original sites in this physical cell. -/
  count : ℕ
  /-- Ordered site list from the public geometry. -/
  order : Fin count ≃ Site
  /-- Merged directory of boxes, physical wiring and reported count addresses. -/
  directory : CellSparse.Directory
  /-- Fully assigned private and incoming bit bank. -/
  bank : ℕ → Bool
  /-- A count is supplied for every genuine gadget ID. -/
  reportLength : directory.reportedCounts.length = U
  /-- One site's observations of signs and selected table IDs. -/
  observed : Site → List (Bool × Option ℕ)
  /-- The actual checker reads the ordered concatenation of the site observations. -/
  reads : directory.observations bank = some ((List.ofFn order).flatMap observed)
  /-- The actual signed assignment passes the cell checker. -/
  pass : directory.weight bank ≠ 0
  /-- Address of the zero word used by the count descriptors. -/
  zeroAddr : ℕ
  /-- Beginning of the address list for a gadget's count word. -/
  references : Fin U → ℕ

/-- The actual operand for the specified gadget's reported count. -/
def CellRead.operand {Site : Type*} {U : ℕ} (c : CellRead Site U) (H : ℕ) (g : Fin U) : Operand :=
  countOperand H c.zeroAddr (c.references g) c.directory c.bank (g.cast c.reportLength.symm)

/-- A passing private call makes the public operand equal the sum of its actual original
site ID frequencies, without consulting any of the associated field scalar values. -/
theorem CellRead.operand_pair {Site : Type*} [Fintype Site] {U : ℕ} (c : CellRead Site U)
    (H : ℕ) (g : Fin U) :
    (c.operand H g).pair = (H+g.val,∑ v : Site, ((c.observed v).filterMap Prod.snd).count g.val) := by
  have eq := CellSparse.merged_countOperand_pair c.directory c.bank (List.ofFn c.order) c.observed
    c.reads c.pass H c.zeroAddr (c.references g) (g.cast c.reportLength.symm)
  change _ = (H+g.val,_) at eq
  unfold operand
  rw [eq,List.map_ofFn,List.sum_ofFn]
  exact congrArg (Prod.mk (H+g.val)) (c.order.sum_comp (fun v => ((c.observed v).filterMap Prod.snd).count g.val))

variable {n d blocks b h K s D B T H U : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
variable (tags : N.Tables (Entry (Fin H) (Fin U))) (x : Ports bits)
variable (pos : Packet n d blocks → TableEntry n b h K s → Fin U)
variable (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
variable (label : Cell → Label (n+1) d) (team : Fin d → Fin T)
variable (a : Path N cell n d blocks b h K s) (t : Fin T)

/-- The actual three chronological lists of owned sources on the currently chosen
minimizing coordinate. Any public ordering of the same rows is permitted. -/
structure Orders where
  /-- Number of owned unary occurrences. -/
  nUse : ℕ
  /-- Number of owned cells. -/
  nCell : ℕ
  /-- Number of owned packet vertices. -/
  nVertex : ℕ
  /-- Every original power slot processed by this team, once. -/
  uses : Fin nUse ≃ {i // routedPowerOwner tags words label team a i = t}
  /-- Every host cell processed by this team, once. -/
  cells : Fin nCell ≃ {c // pathCellOwner label team a c = t}
  /-- Every physical cube vertex processed by this team, once. -/
  vertices : Fin nVertex ≃ {v // pathOwner label team a (.inr v) = t}

variable (o : Orders tags words label team a t) (uses : PowerSlot (Fin T) (Fin H) B → UseRead)
    (cells : ∀ c : Cell, CellRead {v : N.Site // cell v = c} U)
    (packets : Packet n d blocks × Vertex (n+1) → PacketRead)

/-- Native operand list for this team's three actual source tables. Cell count fields
come directly from the private checker and packet offsets use their exact lookup IDs. -/
noncomputable def operands : List Operand :=
  (List.ofFn fun j => let i := (o.uses j).val
    let z := uses i
    unaryOperand z.parameterAddr z.placeAddr z.referenceAddr z.bitAddr i.2.1.val i.2.2.val z.bit) ++
  (List.ofFn fun j => List.ofFn fun g : Fin U => (cells (o.cells j).val).operand H g).flatten ++
  (List.ofFn fun j => let pv := (o.vertices j).val
    let z := packets pv
    packetOperand H z.idAddr z.zeroAddr z.referenceAddr z.oneAddr (pathPacketID pos a pv).val)

private theorem inc_sum (base coord : ℕ) (xs : List Operand) :
    incrementAt base (base+coord) (xs.map Operand.pair) =
      (xs.map (fun z => if z.pair.1 = coord then z.pair.2 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [incrementAt,ih]

omit [Fintype Cell] [DecidableEq Cell] in
/-- One physical descriptor is consumed per unary slot, per cell and gadget ID,
and per routed cube vertex. -/
theorem operands_length :
    (operands tags pos words label team a t o uses cells packets).length = o.nUse + o.nCell*U + o.nVertex := by
  simp [operands,List.length_flatten,List.map_ofFn,Function.comp_def,Nat.add_assoc]

omit [Fintype Cell] in
/-- Every generated operand addresses one of the H parameter or U scalar coordinates. -/
theorem operands_coordinates (op : Operand)
    (hm : op ∈ operands tags pos words label team a t o uses cells packets) : op.pair.1 < H+U := by
  unfold operands at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
      rw [unaryOperand_pair]
      exact ((o.uses i).val.2.1.isLt).trans_le (Nat.le_add_right ..)
    · obtain ⟨xs,hx,hy⟩ := List.mem_flatten.mp hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hy
      rw [CellRead.operand_pair]
      exact Nat.add_lt_add_left g.isLt H
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hm
    rw [packetOperand_pair]
    exact Nat.add_lt_add_left (pathPacketID pos a (o.vertices v).val).isLt H

/-- Actual descriptors may relocate bit addresses and order cell rows differently.
The resulting subtotal depends only on the permutation of their computed coordinate
and increment pairs, while the native execution uses the real descriptor order. -/
theorem increment_pair_perm {xs ys : List Operand} (perm : (xs.map Operand.pair).Perm (ys.map Operand.pair))
    (base c : ℕ) :
    incrementAt base (base+c) (xs.map Operand.pair) = incrementAt base (base+c) (ys.map Operand.pair) := by
  rw [inc_sum,inc_sum]
  simpa only [List.map_map,Function.comp_def] using
    (perm.map (fun z : ℕ × ℕ => if z.1 = c then z.2 else 0)).sum_eq

/-- Exact native subtotal of a physical team at every parameter or gadget coordinate.
The only value identifications concern original site observations and individually
checked use bits. -/
theorem increment_eq_row (base : ℕ) (j : Fin (H+U))
    (useBit : ∀ i, (uses i).bit = words.localUse (pathEdges slot a) (fun _ p => x p.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v = c}) g,
      (((cells c).observed v).filterMap Prod.snd).count g.val =
        (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g) :
    incrementAt base (base+j.val) ((operands tags pos words label team a t o uses cells packets).map Operand.pair) =
      physicalRow slot tags x pos words label team a t j := by
  rw [inc_sum]
  simp only [operands,List.map_append,List.sum_append,List.map_flatten,List.sum_flatten,List.map_ofFn,
    List.sum_ofFn,Function.comp_def,unaryOperand_pair,packetOperand_pair,CellRead.operand_pair,siteID]
  refine Fin.addCases ?_ ?_ j
  · intro p
    simp only [Fin.val_castAdd,physicalRow,Fin.append_left]
    have beyond (g : Fin U) : H+g.val ≠ p.val := by omega
    simp only [ite_eq_right (beyond _),Finset.sum_const_zero,add_zero]
    rw [routedParameterRow,← o.uses.sum_comp (fun i => routedPower slot tags x words a i.val p)]
    apply Finset.sum_congr rfl
    intro i _
    simp [routedPower,slotPower,Finsupp.single_apply,Fin.ext_iff,useBit]
  · intro g
    simp only [Fin.val_natAdd,physicalRow,Fin.append_right]
    have earlier (p : Fin H) : p.val ≠ H+g.val := by omega
    simp only [ite_eq_right (earlier _),Finset.sum_const_zero,zero_add,Nat.add_right_inj,←Fin.ext_iff,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [pathTally_counts_eq_cells_packets,← o.cells.sum_comp (fun c => pathCellCounts slot tags x a c.val g),
      ← o.vertices.sum_comp (fun v => if pathPacketID pos a v.val = g then 1 else 0)]
    rfl

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
