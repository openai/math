import OAI.Computability.BorderVNP.CubeScatterHostPins
import OAI.Computability.BorderVNP.CubeScatterPacketPreservation
import OAI.Computability.BorderVNP.CubeScatterSingletonReadback
import OAI.Computability.BorderVNP.CubeScatterCommonPrepared

/-! # Readback of packet vertices and singleton endpoints across mixed scatter rows

A physical view records either one singleton word or all lookup inputs of a packet
vertex. The ordered symbol pair identifies the team-row iteration that supplies it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical Physical.Owned Physical.VertexIndex HostAddress Scatter RoutingISA
open VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally
open RoutingISA.OwnedVertex (bankAt)

variable {n d blocks b h K s w : ℕ}

/-- Global assignment, packet bank and singleton reservation as seen by this team. -/
structure Data (n d blocks b h K s : ℕ) where
  /-- Chosen grouping coordinate. -/
  axis : Fin (n+1)
  /-- Absolute packet-bank base. -/
  packetBase : ℕ
  /-- Absolute singleton-bank base. -/
  singleBase : ℕ
  /-- Selector of each globally indexed packet. -/
  select : Packet n d blocks → Selector n K h
  /-- Packet demand words in the physical assignment. -/
  demand : Packet n d blocks → Ends n → Fin (h*b) → Bool
  /-- Packet supply words in the physical assignment. -/
  supply : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool
  /-- Singleton words indexed by their actual label pair and ordinal. -/
  value : Label (n+1) d × Label (n+1) d → Fin (blocks*(h*b)) → Bool

/-- A physical local input that must survive the whole native team traversal. -/
inductive View (n d blocks width : ℕ)
  | single (q : SingleSlot n d blocks width) (side : Bool)
  | vertex (p : Packet n d blocks) (v : Vertex (n+1))

variable (A : Data n d blocks b h K s)

/-- Address of a real singleton slot in the linear product-label-pair bank. -/
def Data.singleAddr (q : SingleSlot n d blocks (h*b)) :=
  A.singleBase+(code q.1.val.1*d^(n+1)+code q.1.val.2)*(blocks*(h*b))+q.2.val

/-- Address of the packet bank used by this team's vertex lookups. -/
def Data.packetAddr (p : Packet n d blocks) := bankAt A.packetBase (bankWidth n b h K s) p

/-- Native words read by a correct local view. -/
def Data.Holds (m : Memory w) : View n d blocks (h*b) → Prop
  | .single q _ => m (A.singleAddr q) = wordBit w (A.value q.1.val q.2)
  | .vertex p v => VertexAt m (A.packetAddr p) (A.select p) v (A.demand p) (A.supply p)

/-- Ordered symbol row, starting with the owned endpoint's group. -/
def View.row (axis : Fin (n+1)) : View n d blocks (h*b) → Fin d × Fin d
  | .single q side =>
    if side then (q.1.val.2 axis,q.1.val.1 axis) else (q.1.val.1 axis,q.1.val.2 axis)
  | .vertex p v =>
    if cornerBits p v axis then ((p.1.1 axis).val.2,(p.1.1 axis).val.1)
    else ((p.1.1 axis).val.1,(p.1.1 axis).val.2)

/-- The first symbol of the visiting packet row is precisely its endpoint's physical owner symbol. -/
theorem View.vertex_row_owner (axis : Fin (n+1)) (p : Packet n d blocks) (v : Vertex (n+1)) :
    ((View.vertex p v : View n d blocks (h*b)).row axis).1 = vertexLabel p v axis := by
  by_cases c : cornerBits p v axis <;> simp [View.row,vertexLabel,c]

/-- The actual per-row scatter data before a packet stage. -/
def Data.packet (pair : Symbols d) (high : Bool) (sel cross : ℕ) : PacketRowData n d blocks b h K s :=
  ⟨A.axis,pair,high,A.packetBase,bankWidth n b h K s,sel,cross,A.select,A.demand,A.supply⟩

/-- The actual singleton row data used on the diagonal or after the packet stage. -/
def Data.single (left right : Fin d) (sel cross : ℕ) : SingleRowData n d (blocks*(h*b)) :=
  ⟨A.axis,left,right,A.singleBase,sel,cross,A.value⟩

/-- The two physical reservations are disjoint on the addressed packet rectangles. -/
def Data.Separate : Prop := ∀ p : Packet n d blocks,
  A.packetAddr p+bankWidth n b h K s ≤ A.singleBase ∨
    A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ A.packetAddr p

/-- Transport a vertex's entire native lookup across agreement on its packet bank. -/
theorem Data.vertex_congr {m m' : Memory w} (p : Packet n d blocks) (v : Vertex (n+1))
    (eq : ∀ j : Fin (bankWidth n b h K s), m' (A.packetAddr p+j.val) = m (A.packetAddr p+j.val))
    (old : A.Holds m (.vertex p v)) : A.Holds m' (.vertex p v) := by
  constructor
  · intro j
    have bound : j.val < bankWidth n b h K s := by unfold bankWidth supplyBase; have := j.isLt; omega
    exact (congrArg Fin.val (eq ⟨_,bound⟩)).trans (old.selector j)
  · intro e hit j
    have range := (demandOffset_range (K := K) e j).2
    have bound : demandOffset n b h K e j < bankWidth n b h K s := by unfold bankWidth; omega
    exact (congrArg Fin.val (eq ⟨_,bound⟩)).trans (old.demand e hit j)
  · intro e hit j
    exact (congrArg Fin.val (eq ⟨_,(supplyOffset_range (b := b) (A.select p) e j).2⟩)).trans (old.supply e hit j)

/-- A singleton stage preserves all previously correct physical views, including those
in the disjoint packet reservation and those revisited from another owned endpoint. -/
theorem Data.single_keeps (sep : A.Separate) (left right : Fin d) (sel cross : ℕ)
    (m : Memory w) (x : View n d blocks (h*b)) (old : A.Holds m x) :
    A.Holds (((A.single left right sel cross).before m (singlePairTrials n d)).2) x := by
  let D := A.single left right sel cross
  cases x with
  | single q side => exact D.final_preserves_correct m q.1.val q.2 old
  | vertex p v =>
    apply A.vertex_congr p v _ old
    intro j
    apply D.final_outside
    have hj := j.isLt
    change _ < A.singleBase ∨ A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ _
    rcases sep p with small | large <;> omega

private theorem singleAddr_range (q : SingleSlot n d blocks (h*b)) :
    A.singleBase ≤ A.singleAddr q ∧ A.singleAddr q < A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) := by
  let k := code q.1.val.1*d^(n+1)+code q.1.val.2
  have lt : k < d^(n+1)*d^(n+1) := by
    have he := (finProdFinEquiv (finFunctionFinEquiv q.1.val.1,finFunctionFinEquiv q.1.val.2)).isLt
    change code q.1.val.2 + d^(n+1)*code q.1.val.1 < _ at he
    simpa only [k,Nat.mul_comm,Nat.add_comm] using he
  have lim := Nat.mul_le_mul_right (blocks*(h*b)) lt
  rw [Nat.succ_mul] at lim
  have hj := q.2.isLt
  change A.singleBase ≤ A.singleBase+k*(blocks*(h*b))+q.2.val ∧ _
  change _ ∧ A.singleBase+k*(blocks*(h*b))+q.2.val < _
  omega

/-- A packet stage preserves every previously correct singleton and every previously
correct vertex, even if the two opposing symbol groups are assigned to the same team. -/
theorem Data.packet_keeps (sep : A.Separate) (hw : 0 < w) (pair : Symbols d) (high : Bool)
    (sel cross : ℕ) (m : Memory w) (x : View n d blocks (h*b)) (old : A.Holds m x) :
    A.Holds (((A.packet pair high sel cross).before m (packetTrials n d blocks)).mem) x := by
  let D := A.packet pair high sel cross
  cases x with
  | vertex p v => exact D.before_preserves_vertexAt p v m hw le_rfl old _ le_rfl
  | single q side =>
    apply D.before_invariant m (fun u => u (A.singleAddr q) = wordBit w (A.value q.1.val q.2)) old _ _ le_rfl
    intro p _ z hold
    rw [D.visit_outside p z _ ?_]
    · exact hold
    have bounds := singleAddr_range A q
    change A.singleAddr q < A.packetAddr p ∨ A.packetAddr p+bankWidth n b h K s ≤ A.singleAddr q
    rcases sep p with small | large <;> omega

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
