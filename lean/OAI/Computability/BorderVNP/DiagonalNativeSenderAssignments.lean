import OAI.Computability.BorderVNP.DiagonalNativePreparedRoute
import OAI.Computability.BorderVNP.TransmissionSenderCount

/-! # Removing the sender predicate from the local choice domain

The true source and routed word are independent of the team's locally guessed wires
when those words lie outside every earlier write. Thus a failed sender check rejects
all guesses, and otherwise every fixed-width local word has its own complete return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ} {f : BroadcastFrame} (rows : ℕ → Range w) (pub : Arg → Word w) (m : Memory w)
    (frame : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (sep : ∀ i < (directoryFrame pub m 13).val, (rows i).scheduleSeparated (directoryFrame pub m 0) pub m f.teams)
    (peer : ∀ i < (directoryFrame pub m 13).val, (rows i).teamB.val < f.teams)
    (kept : ∀ k < (directoryFrame pub m 13).val, (rows k).selected (directoryFrame pub m 0) = some (some .sendData) →
      ∀ j < (rows k).width.val, ∀ i < k, (rows i).protectsCell (directoryFrame pub m 0) ((rows k).source.val+j) ∧
        (rows i).protectsCell (directoryFrame pub m 0) ((rows k).senderAddress pub m j))

/-- The single chronological Boolean string naming the local shared-wire choices. -/
abbrev LocalSlots := Fin (choiceOffset rows (directoryFrame pub m 0) (directoryFrame pub m 13).val) → Bool

/-- The physical sender check before any destination is written. -/
def SendersMatch : Prop :=
  ∀ i < (directoryFrame pub m 13).val, (rows i).senderMatches (directoryFrame pub m 0) pub m

include frame fit sep peer kept in
/-- The typed sender predicate on each actual guessed word is precisely the original
read-only comparison. Both addresses are preserved through all preceding writes. -/
theorem localSlots_check (b : LocalSlots rows pub m) :
    (∀ i < (directoryFrame pub m 13).val, (rows i).senderMatches (directoryFrame pub m 0) pub
      (tableMemory rows (directoryFrame pub m 0) pub m (decodeChoices rows (directoryFrame pub m 0) (List.ofFn b)) i)) ↔
      SendersMatch rows pub m := by
  have ht : (directoryFrame pub m 0).val = f.team := by simpa [directoryFrame,frameField,readings] using frame.1
  exact forall_congr' fun i => forall_congr' fun hi =>
    table_senderMatches_stable rows _ pub m _ i frame fit ht (fun j hj => sep j (hj.trans hi)) (peer i hi) (kept i hi)

/-- On true sender words the reindexing changes only the proofs carried by the subtype. -/
def localSlotsEquiv (yes : SendersMatch rows pub m) :
    LocalSlots rows pub m ≃ SenderWords rows pub m where
  toFun b := ⟨b,(localSlots_check rows pub m frame fit sep peer kept b).mpr yes⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

include frame fit sep peer kept in
/-- An incorrect physical sender word rejects the entire local choice domain. -/
theorem noSenderWords (bad : ¬ SendersMatch rows pub m) : IsEmpty (SenderWords rows pub m) :=
  ⟨fun b => bad ((localSlots_check rows pub m frame fit sep peer kept b.val).mp b.property)⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
