import OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide
import OAI.Computability.BorderVNP.CubeTeamRowPrepare

/-! # Address bounds shared by all owned views of the native team loop

The primary and secondary headers precede the packet array. The power
table and ordered shared buffers may also follow the whole vertex directory.
Every store to a packet or singleton is separated from those actual sources.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowSources

open Physical Physical.Owned Scatter RoutingISA RoutingISA.OwnedStages VPVNP.BurstRAM Tally
open Padding.Banks
open private packet_end_le from OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

variable {w n d blocks b h K s : ℕ} (A : Data n d blocks b h K s) (l : TeamRowPrepare.Layout)

/-- The primary/secondary headers, alphabet powers, and actual ordered endpoint views. -/
def source (power n : ℕ) : Set ℕ :=
  (Set.Ico (l.header+13+l.d*l.d*(n+1)) (l.header+13+2*(l.d*l.d*(n+1))+(n+1)) ∪
    Set.Ico l.ownerBase (l.ownerBase+l.d)) ∪ (
  Set.Ico l.frame (l.frame+112) ∪ Set.Ico l.header (l.header+13) ∪
    Set.Ico power (power+n+1) ∪ Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d)))

/-- Common header and address arithmetic used for either directed role of a symbol pair. -/
def rowLayout (power : ℕ) : OwnedRowSetup.Layout := ⟨d,blocks,h*b,power,l.header,A.packetBase⟩

/-- Allocation of the true physical data and all immutable inputs. Each
condition refers to one complete contiguous range, independent of any row. -/
structure Allocation (power vertexBase stop w : ℕ) : Prop where
  /-- Numeric conditions for reading the frame and iterating the local packet counters. -/
  packets : PacketRoom (rowLayout A l power) w n b h K s l.frame
  /-- The product-label key and whole singleton reservation fit in one word. -/
  singles : SingleRoom w n d (blocks*(h*b)) l.frame A.singleBase
  /-- The singleton array follows every packet rectangle. -/
  orderPackets : A.packetBase+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ A.singleBase
  /-- Vertex records follow every ordered singleton. -/
  orderSingles : A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ vertexBase
  /-- The directory sentinel is an actual machine word. -/
  endFit : stop < 2^w
  /-- The whole primary frame precedes the packet reservation. -/
  frame : l.frame+112 ≤ A.packetBase
  /-- All secondary header words precede the packet reservation. -/
  header : l.header+13 ≤ A.packetBase
  /-- Both dense declaration tables and all public totals precede the packet bank. -/
  declaration : l.header+13+2*(l.d*l.d*(n+1))+(n+1) ≤ A.packetBase
  /-- The greedy group owner array lies outside all scatter and directory writes. -/
  owners : l.ownerBase+l.d ≤ A.packetBase ∨ stop ≤ l.ownerBase
  /-- The powers lie outside the complete scatter and directory interval. -/
  powers : power+n+1 ≤ A.packetBase ∨ stop ≤ power
  /-- All ordered endpoint views lie outside the complete scatter and directory interval. -/
  views : l.viewBase+l.stride*(l.d*l.d) ≤ A.packetBase ∨ stop ≤ l.viewBase

variable {A l} {power vertexBase stop : ℕ}

/-- The setup code reads the actual header words and powers from this source. -/
theorem frame_protected : Protected (rowLayout A l power) n l.frame (source l power n) := by
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · intro j hj
    have upper : j < 112 := by simp at hj; omega
    exact Or.inr (Or.inl (Or.inl (Or.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left upper _⟩)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left (by decide : 7 < 13) _⟩)))
  · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left (by decide : 8 < 13) _⟩)))
  · intro j hj
    exact Or.inr (Or.inl (Or.inr ⟨Nat.le_add_right ..,by change power+j < power+n+1; omega⟩))

/-- Every primary frame word is in the preserved source. -/
theorem primary {j : ℕ} (hj : j < 112) : l.frame+j ∈ source l power n :=
  Or.inr (Or.inl (Or.inl (Or.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)))

/-- Each source address lies entirely before the packet array or beyond
the global vertex-directory sentinel, independently of the current side. -/
theorem Allocation.outside (a : Allocation A l power vertexBase stop w) {j : ℕ}
    (hj : j ∈ source l power n) : j < A.packetBase ∨ stop ≤ j := by
  rcases hj with (decl | owner) | (((frame | header) | powers) | views)
  · exact Or.inl (decl.2.trans_le a.declaration)
  · exact a.owners.elim (fun low => Or.inl (owner.2.trans_le low)) (fun hi => Or.inr (hi.trans owner.1))
  · exact Or.inl (frame.2.trans_le a.frame)
  · exact Or.inl (header.2.trans_le a.header)
  · exact a.powers.elim (fun low => Or.inl (powers.2.trans_le low)) (fun hi => Or.inr (hi.trans powers.1))
  · exact a.views.elim (fun low => Or.inl (views.2.trans_le low)) (fun hi => Or.inr (hi.trans views.1))

/-- Every physical packet write in every selected row is in its actual
allocated rectangle, outside all immutable sources. -/
theorem Allocation.packetDest (a : Allocation A l power vertexBase stop w) (space : vertexBase ≤ stop)
    (p : Packet n d blocks) {j : ℕ} (hj : j < bankWidth n b h K s) :
    A.packetAddr p+j ∉ source l power n ∧ A.packetAddr p+j < 2^w := by
  have lo : A.packetBase ≤ A.packetAddr p := Nat.le_add_right ..
  have hi := (Nat.add_lt_add_left hj (A.packetAddr p)).trans_le ((packet_end_le A p).trans a.orderPackets)
  have lim := (Nat.le_add_right _ _).trans (a.orderSingles.trans space)
  exact ⟨fun inside => (a.outside inside).elim (by omega) (by omega),(hi.trans_le lim).trans a.endFit⟩

/-- Every ordered label pair has a represented destination interval disjoint
from the immutable inputs, including pairs outside the selected direction. -/
theorem Allocation.singleDest (a : Allocation A l power vertexBase stop w) (space : vertexBase ≤ stop)
    (u v : Label (n+1) d) {j : ℕ} (hj : j < blocks*(h*b)) :
    let addr := singleBase A.singleBase (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv v).val+j
    addr ∉ source l power n ∧ addr < 2^w := by
  intro addr
  let k := (finFunctionFinEquiv u).val*d^(n+1)+(finFunctionFinEquiv v).val
  have hk : k < d^(n+1)*d^(n+1) := by
    have hi := (finProdFinEquiv (finFunctionFinEquiv u,finFunctionFinEquiv v)).isLt
    change (finFunctionFinEquiv v).val+d^(n+1)*(finFunctionFinEquiv u).val < _ at hi
    simpa only [k,Nat.mul_comm,Nat.add_comm] using hi
  have step := Nat.mul_le_mul_right (blocks*(h*b)) hk
  rw [Nat.succ_mul] at step
  change A.singleBase+k*(blocks*(h*b))+j ∉ _ ∧ A.singleBase+k*(blocks*(h*b))+j < _
  have room := a.orderSingles.trans space
  have lower := (Nat.le_add_right ..).trans a.orderPackets
  exact ⟨fun inside => (a.outside inside).elim (by omega) (by omega),by have := a.endFit; omega⟩

/-- Shared input words remain resident when the source is enlarged to include
the header and power-table fields of the current team. -/
theorem resident_views {m : Memory w} {ptr : ℕ} {xs : List Bool}
    (read : Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) m ptr xs) :
    Resident (source l power n) m ptr xs :=
  ⟨read.bits,fun j hj => ⟨Or.inr (Or.inr (read.addresses j hj).1),(read.addresses j hj).2⟩⟩

end Cube.TeamRowSources

end BorderVNP
end Computability
end OAI
