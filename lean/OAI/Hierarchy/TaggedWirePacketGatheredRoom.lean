import OAI.Hierarchy.TaggedWirePacketShiftedRows
import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWireAggregatePrefix
import OAI.Hierarchy.TaggedWirePacketCodes

namespace OAI
/-! # Fixed bounds on gathered chord digits, role numbers and every populated packet field -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open TurnShelf Tagged ChosenPackets.RowRouting
open scoped Classical BigOperators

variable {S n m t count D K W : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (ord : Fin t≃Σi,Fin (route i).length)
local notation "mass" => routeLoad route bits
local notation "shift" => AggregatePrefix.paidShift route bits ord edge

include ord in
theorem chord_room (cap : ℕ) (bounded : ∀i,bits i≤cap) (ch : Chord S) :
    installedWidths edge mass ch≤t*cap := by
  rw [←AggregatePrefix.chordTotal_eq_width route bits ord edge ch]
  unfold AggregatePrefix.chordTotal
  calc _≤∑ _ : Fin t,cap := by
         apply Finset.sum_le_sum
         intro u _
         split
         · exact bounded _
         · exact Nat.zero_le _
       _=t*cap := by simp

variable {s : Fin S} {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
    (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route)
local notation "before" => fun (i : Fin n) (b : Bool)=>(halfCode i b).val
local notation "after" => fun (e : Fin m) (b : Bool)=>n*2+PacketNeighbor.index parts ((rowGraph edge).vertex e (!b))
local notation "col" => shiftedFields old edge route bits ord shift before after short turns

theorem gathered_fits (sectors : n*2+D<2^W) (widths : ∀i,bits i<2^W)
    (chords : ∀e,installedWidths edge mass (edge e)≤2^W) :
    ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W := by
  intro u f
  let i:=(turns u.val).1
  have live : 0<bits i:=Nat.pos_of_ne_zero u.property
  have sector (a : TurnRef) : refRole route before after i a<2^W := by
    rcases a with b|⟨j,b⟩
    · exact (halfCode i b).isLt.trans_le ((Nat.le_add_right _ _).trans sectors.le)
    · simp only [refRole]
      split
      · exact (Nat.add_le_add_left (PacketNeighbor.index_le parts _) _).trans_lt sectors
      · exact Nat.two_pow_pos _
  have «prefix» (a : TurnRef) : shiftedStart route bits ord shift i a<2^W := by
    rcases a with b|⟨j,b⟩
    · exact Nat.two_pow_pos _
    · simp only [shiftedStart]
      split
      next h=>
        let q : Fin (route i).length:=⟨j,h⟩
        let e:=(route i).get q
        have start : NativeSlot.start route bits ord i q+bits i≤ mass e :=
          NativeSlot.start_room route bits ord i q live
        have bounded : shift e+mass e≤2^W:=(AggregatePrefix.shift_room route bits ord edge e).trans (chords e)
        change shift e+NativeSlot.start route bits ord i q<2^W
        omega
      · exact Nat.two_pow_pos _
  fin_cases f <;> first | exact sector _ | exact «prefix» _ | exact widths i

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
