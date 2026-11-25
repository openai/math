import OAI.Computability.BorderVNP.CubeScatterPacketPrepared
import OAI.Computability.BorderVNP.CubeScatterSinglePrepared
import OAI.Computability.BorderVNP.CubeScatterSharedStreams

/-! # Three physical scatter passes on the actual delivered strict-row words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.PacketRowData

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

/-- The ordered singleton pass starts at the cursors returned by its predecessor. -/
def singletonRow (a t : Fin d) (bank sel cross : ℕ)
    (value : Label (n+1) d × Label (n+1) d → Fin (blocks*(h*b)) → Bool) : SingleRowData n d (blocks*(h*b)) :=
  ⟨D.axis,a,t,bank,sel,cross,value⟩

/-- Starting with the actual two common words of a strict row, the packet pass
and both singleton orientations meet their native preparation conditions in their
own successive memories. The final crossing cursor reaches the declared suffix
end and the original protected words survive all three passes. -/
theorem strictRows_prepared (src : Set ℕ) (m : Memory w) (bank : ℕ)
    (value : Label (n+1) d × Label (n+1) d → Fin (blocks*(h*b)) → Bool)
    (sels : Resident src m D.selector (commonSelectors D.select D.axis D.pair))
    (cross : Resident src m D.crossing (commonCrossings b D.axis D.pair D.select D.supply (fun z => value z.1.val z.2)))
    (packetDest : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair → ∀ j < bankWidth n b h K s,
      OwnedVertex.bankAt D.base D.stride p+j ∉ src ∧ OwnedVertex.bankAt D.base D.stride p+j < 2^w)
    (singleDest : ∀ u v : Label (n+1) d, ∀ j < blocks*(h*b),
      let addr := singleBase bank (d^(n+1)) (blocks*(h*b)) (finFunctionFinEquiv u).val (finFunctionFinEquiv v).val+j
      addr ∉ src ∧ addr < 2^w) :
    let endP := D.before m (packetTrials n d blocks)
    let first := D.singletonRow D.pair.val.1 D.pair.val.2 bank endP.sel endP.cross value
    let endA := first.before endP.mem (singlePairTrials n d)
    let second := D.singletonRow D.pair.val.2 D.pair.val.1 bank endP.sel endA.1 value
    let endB := second.before endA.2 (singlePairTrials n d)
    D.PreparedRow src m ∧ first.PreparedRow src endP.mem ∧ second.PreparedRow src endA.2 ∧
      endB.1 = D.crossing+(commonCrossings b D.axis D.pair D.select D.supply (fun z => value z.1.val z.2)).length ∧
      ∀ j ∈ src, endB.2 j = m j := by
  intro endP first endA second endB
  let ps := (packetVisits blocks D.axis D.pair).flatMap (fun p => crossingStream b (D.select p) D.axis (D.supply p))
  let lo := (singleVisits blocks (h*b) D.axis D.pair.val.1 D.pair.val.2).map (fun z => value z.1.val z.2)
  let hi := (singleVisits blocks (h*b) D.axis D.pair.val.2 D.pair.val.1).map (fun z => value z.1.val z.2)
  change Resident src m D.crossing (ps++lo++hi) at cross
  have pstream : Resident src m D.crossing ps := by
    simpa only [List.length_nil,Nat.add_zero] using Resident.slice [] ps (lo++hi)
      (by simpa only [List.nil_append,List.append_assoc] using cross : Resident src m D.crossing ([]++ps++(lo++hi)))
  have prepP := D.preparedRow_of_streams src m sels pstream packetDest
  have sourceP : ∀ j ∈ src, endP.mem j = m j := D.before_source m prepP _
  have cursorP : endP.cross = D.crossing+ps.length := (D.final_cursors m).2
  have firstWords : first.crossingWords = lo := ite_eq_right D.pair.property.ne
  have firstRead : Resident src endP.mem first.crossing first.crossingWords := by
    change Resident src endP.mem endP.cross first.crossingWords
    rw [cursorP,firstWords]
    exact (Resident.slice ps lo hi cross).congr sourceP
  have prepA := first.preparedRow_of_streams src endP.mem firstRead (fun t _ => singleDest (first.pair t).1 (first.pair t).2)
  have sourceA : ∀ j ∈ src, endA.2 j = m j := fun j hj => (first.before_source endP.mem prepA _ j hj).trans (sourceP j hj)
  have cursorA : endA.1 = D.crossing+ps.length+lo.length := by
    rw [show endA.1 = endP.cross+first.crossingWords.length from first.final_cursor endP.mem,cursorP,firstWords]
  have secondWords : second.crossingWords = hi := ite_eq_right D.pair.property.ne'
  have secondRead : Resident src endA.2 second.crossing second.crossingWords := by
    change Resident src endA.2 endA.1 second.crossingWords
    rw [cursorA,secondWords]
    have bits := Resident.slice (ps++lo) hi [] (by simpa only [List.append_nil] using cross : Resident src m D.crossing ((ps++lo)++hi++[]))
    simpa only [List.length_append,Nat.add_assoc] using bits.congr sourceA
  have prepB := second.preparedRow_of_streams src endA.2 secondRead (fun t _ => singleDest (second.pair t).1 (second.pair t).2)
  refine ⟨prepP,prepA,prepB,?_,fun j hj => (second.before_source endA.2 prepB _ j hj).trans (sourceA j hj)⟩
  change endB.1 = D.crossing+(ps++lo++hi).length
  rw [show endB.1 = endA.1+second.crossingWords.length from second.final_cursor endA.2,cursorA,secondWords]
  simp only [List.length_append,Nat.add_assoc]

end Cube.Scatter.PacketRowData

end BorderVNP
end Computability
end OAI
