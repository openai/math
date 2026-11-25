import OAI.Computability.BorderVNP.CubeISAOwnedRawDoubleStage
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSide
import OAI.Computability.BorderVNP.CubeISALocalRowSpace

/-! # Selector-bank and source retention to the end of an arbitrary strict-side return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Physical Cube.Physical.Owned Cube.Scatter Cube.Tally VPVNP.BurstRAM Owned OwnedVertex

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)

/-- Geometric and word-size data for the singleton scatters and vertex output. The routed
crossing stream has no value or length precondition here. -/
structure RawTailRoom (pub : Arg → Word w) (src : Set ℕ) : Prop where
  /-- Stable packet stride. -/
  stride : D.stride = bankWidth n b h K s
  /-- Ordinary scalar and packet-loop word room. -/
  fit : PacketRoom (layout D A.power A.header) w n b h K s (pub 0).val
  /-- Word room for each actual singleton family. -/
  single : SingleRoom w n d (blocks*(h*b)) (pub 0).val A.bank
  /-- The physically addressed frame and power words are protected. -/
  frame : Protected (layout D A.power A.header) n (pub 0).val src
  /-- Both singleton lookup fields are protected. -/
  fields : (pub 0).val+56 ∈ src ∧ (pub 0).val+88 ∈ src
  /-- Singleton stores do not alias the protected source words. -/
  dest : ∀ u v : Label (n+1) d, ∀ j < blocks*(h*b),
    singleBase A.bank (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv v).val+j ∉ src
  /-- Packet slots precede all singleton writes. -/
  beforeSingle : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.bank
  /-- Packet slots precede all vertex writes. -/
  beforeVertices : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.out
  /-- Directory end fits a word. -/
  directory : A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) < 2^w
  /-- Vertex-directory writes miss the designated source words. -/
  separated : ∀ x ∈ src, x < A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ x

/-- Arbitrary actual singleton and vertex returns retain the previously decoded selector
slots. Their input source words may have any values, and the crossing cursor may be anywhere. -/
theorem rawTail_return {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} (src : Set ℕ)
    {r : Bank w} {m : Memory w} {es u mu fs t mt}
    (entry : Entry D.axis D.pair.val.1 D.pair.val.2 r)
    (group : readings r 3 = (if D.high then D.pair.val.2 else D.pair.val.1).val)
    (output : readings r 7 = A.out) (loaded : (layout D A.power A.header).Loaded n (readings pub) (readings m))
    (zAt : readings m ((pub 0).val+56) = d^(n+1)) (bankAt : readings m ((pub 0).val+88) = A.bank)
    (room : RawTailRoom D A pub src)
    (stored : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair →
      SelectorRead.Stored (readings m) (OwnedVertex.bankAt D.base D.stride p) (D.select p))
    (doubleRun : Runs pub mac (doubleStage n) r m es u mu)
    (vertexRun : Runs pub mac (vertexStage n b h K s) u mu fs t mt) :
    (∀ j, Control j → j ≠ 7 → t j = r j) ∧ t 36 = r 36 ∧
      readings t 7 = A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ∧ (∀ x ∈ src, mt x = m x) ∧
      ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair →
        SelectorRead.Stored (readings mt) (OwnedVertex.bankAt D.base D.stride p) (D.select p) := by
  let L := layout D A.power A.header
  let keepSet := src ∪ {x : ℕ | x < A.bank}
  let one := D.singletonRow D.pair.val.1 D.pair.val.2 A.bank 0 0 A.value
  let two := D.singletonRow D.pair.val.2 D.pair.val.1 A.bank 0 0 A.value
  have frame : Protected L n (pub 0).val keepSet := ⟨fun j hj => .inl (room.frame.fields j hj),
    ⟨.inl room.frame.secondary.1,.inl room.frame.secondary.2⟩,fun j hj => .inl (room.frame.powers j hj)⟩
  have sep (X : SingleRowData n d (blocks*(h*b))) (bank : X.bank = A.bank) (k : Fin (singlePairTrials n d))
      (x : ℕ) (hx : x ∈ keepSet) : x < X.address k ∨ X.address k+blocks*(h*b) ≤ x := by
    rcases hx with hs|low
    · by_contra! wrong
      have off : x-X.address k < blocks*(h*b) := by omega
      have ban := room.dest (X.pair k).1 (X.pair k).2 (x-X.address k) off
      rw [← bank] at ban
      change X.address k + (x-X.address k) ∉ src at ban
      rw [show X.address k+(x-X.address k) = x by omega] at ban
      exact ban hs
    · change x < A.bank at low
      exact .inl (low.trans_le (by simp [SingleRowData.address,singleBase,bank]))
  obtain ⟨controls,sel,retained⟩ := doubleStage_raw_frame L one two keepSet entry rfl rfl rfl rfl loaded
    room.fit.layout frame (.inl room.fields.1) (.inl room.fields.2) zAt bankAt room.single
    (fun k _ => sep one rfl k) (fun k _ => sep two rfl k) doubleRun
  have old (x : ℕ) (hx : x ∈ src) := retained x (.inl hx)
  have below (p : Packet n d blocks) (j : Fin (selectorWidth n K h)) :
      OwnedVertex.bankAt D.base D.stride p+j.val < D.base+(d*d)^(n+1)*2*blocks*D.stride := by
    have bound := (LocalRow.packetWord_between (l := L) (b := b) (s := s) p j).2
    rw [LocalRow.head_eq] at bound
    simpa only [L,layout,OwnedVertex.bankAt,room.stride] using bound
  have prefixRetained (p : Packet n d blocks) (row : p.1.1 D.axis = D.pair) :
      SelectorRead.Stored (readings mu) (OwnedVertex.bankAt D.base D.stride p) (D.select p) :=
    fun j => (congrArg Fin.val (retained _ (.inr ((below p j).trans_le room.beforeSingle)))).trans (stored p row j)
  have forward := vertexStage_run L D pub mac u mu A.out (entry.keep controls)
    ((congrArg Fin.val (controls 3 (by decide))).trans group) (room.frame.loaded loaded old) room.fit rfl room.stride
    ((congrArg Fin.val (controls 7 (by decide))).trans output) room.beforeVertices room.directory prefixRetained
  obtain ⟨_,_,_,native,_,_,rest,s36,_,cursor,image⟩ := forward
  obtain ⟨_,rfl,rfl⟩ := native.unique_of_deterministic (vertexStage_deterministic ..) vertexRun
  let N := packetTrials n d blocks
  have low := (rowImage_frame (blocks := blocks) D.axis D.pair D.high D.base D.stride (selectorWidth n K h) A.out (readings mu) N).2
  have high := rowImage_above (blocks := blocks) D.axis D.pair D.high D.base D.stride (selectorWidth n K h) A.out (readings mu) N
  dsimp only at high
  rw [rowImage_cursor,selectedPrefix_end] at high
  refine ⟨fun j hj h7 => (rest j hj h7).trans (controls j hj),s36.trans sel,cursor,?_,?_⟩
  · intro x hx
    have same := (room.separated x hx).elim (low x) (high x)
    exact (Fin.ext ((congrFun image x).trans same)).trans (old x hx)
  · intro p row j
    exact ((congrFun image _).trans (low _ ((below p j).trans_le room.beforeVertices))).trans (prefixRetained p row j)

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
