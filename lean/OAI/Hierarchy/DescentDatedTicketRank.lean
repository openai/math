import OAI.Hierarchy.DescentDatedLocalDonorDigit
import OAI.Hierarchy.DescentDatedPriorHeaderReceipt
import OAI.Hierarchy.DescentOrdinaryRawObservedWords

namespace OAI
/-! # The receiver's original raw rank and the local private operand name -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket
open DescentHaloWalkRAM DescentHaloPackedRebase DescentHaloDonorChart DescentSharedCableNames
open DescentPacking.PackedMatch.Local DescentHostDirectory DescentParallelBase
open DescentColonies DescentCableDonorNames DescentSIMDLookup DescentRawCablePanel DescentRawCablePanel.DepotRAM
open DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
  (s : Shape) (u : Material.Setup) (near : V → Finset V) (name : V ↪ Fin H)
  (R : Fin H → Fin s.degree → Option (Fin H)) (listed : ∀v v',v'∈near v → ∃i,R (name v) i=some (name v'))
  («mutual» : ∀v v' i,R v i=some v' → ∃j,R v' j=some v)
  (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun v=>(pos v,block v))
  (whereAt : C → Key (J×V)) (recv : C) (donor : U)
include «mutual»

/-- Raw material field 4 is the word written in the original reverse
rank column, addressed at the donor host by the selected forward path. -/
theorem capture_rank_word {w G M : ℕ} (base : ℕ) (adj : Bank)
    (ok : PriorHeader.Room adj H G M s.degree base w) (m : Memory w)
    (old : ∀(v : Fin H) (i : Fin s.degree),m (adj.base+v.val*s.degree+i.val)=(number (R v i):Word w))
    (sender receiver : Fin H) (parts : Parts s) (seat : Material.Seat s) (p : Fin (breadth s.degree))
    (held : rawAtSeat s u.profile u.motifWidth u.slots false parts seat.1 seat.2.1 seat.2.2=Packed.token (some p))
    (hit : walk R sender (path p) 4=some receiver) (fits : breadth s.degree ≤ 2^u.fieldBits) :
    (Material.rawObserved s u parts (digest (Material.reverseEntries s R sender)) seat 4).val =
      (PriorHeader.image H G M s.degree base adj m
        ((PriorHeader.rankBanks H G M s.degree base).reverseRank.base+(Ranks.id sender p).val)).val :=by
  obtain ⟨q,back,_,rank⟩:=Rebase.actual R «mutual» sender receiver p hit
  have terminal : Rebase.terminal R receiver q=sender.val:=by simp [Rebase.terminal,back,number]
  have bound:=Ranks.bound (Rebase.terminal R) receiver q
  rw [terminal] at bound
  rw [Material.raw_reverse_rank s u parts seat R «mutual» sender receiver p held hit,
    (PriorHeader.directory base adj ok m R old).reverse,
    Fin.val_cast_of_lt ((Rebase.value_le R .rank sender p).trans_lt ok.paths),rank,
    Fin.val_cast_of_lt (bound.trans_le fits)]

theorem capture_donor (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member recv) (parts : Parts s) (seat : Material.Seat s)
    (p : Fin (breadth s.degree))
    (held : rawAtSeat s u.profile u.motifWidth u.slots false parts seat.1 seat.2.1 seat.2.2=Packed.token (some p))
    (hit : walk R (name (pos donor).2) (path p) 4=some (name (whereAt recv).1.2)) (fits : breadth s.degree ≤ 2^u.fieldBits) :
    let observed:=Material.rawObserved s u parts (digest (Material.reverseEntries s R (name (pos donor).2))) seat
    (observed 4).val*2^k+(block donor).val=((DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot recv ⟨donor,inside⟩).val :=by
  dsimp only
  rw [Material.raw_reverse_rank s u parts seat R «mutual» (name (pos donor).2) (name (whereAt recv).1.2) p held hit]
  obtain ⟨numeric,amount⟩:=DescentOrdinaryDonorHalo.Digit.measured_slot near name R listed pos block coords whereAt recv donor inside
  rw [Fin.val_cast_of_lt (numeric.trans_le fits)]
  exact amount

end
end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
