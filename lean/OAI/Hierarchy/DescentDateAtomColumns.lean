import OAI.Hierarchy.DescentDatePortPaidRoom

namespace OAI
/-! # The actual atom bank at each returned venue -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentCompiler DescentDatedSeedStartup DescentColonies ProtocolRAM
noncomputable section

/-- Each atom count is read from the bank at the current row. -/
def AtomColumns (p : DatePorts) (k : ℕ) : Prop :=
  ∀j : Fin (2^k),∃b : Bank,p.io.atoms j.val=.lookup b .row

theorem AtomColumns.work {p : DatePorts} {k : ℕ} (columns : p.AtomColumns k) (j : Fin (2^k)) :
    (p.io.atoms j.val).work=7 := by
  obtain ⟨b,read⟩:=columns j
  rw [read]
  rfl

theorem PaidRoom.atom_columns {p : DatePorts} {w floor : ℕ} (room : p.PaidRoom w floor) (k : ℕ) :
    p.AtomColumns k := fun j=>⟨DescentFundedCensus.priorBank p.io j.val,room.issued.row j.val⟩

theorem initial_atom_columns {F : Type} [Field F] {cp pins : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F cp pins) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups payload Z : ℕ) :
    (initial G op X R l k H groups payload Z).AtomColumns k := by
  intro j
  exact ⟨_,rfl⟩

theorem ordinary_atom_columns {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor k : ℕ) :
    (ordinary v floor).AtomColumns k := by
  intro j
  exact ⟨_,rfl⟩

theorem reset_atom_columns {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w) (k : ℕ) :
    (reset a floor u).AtomColumns k := by
  intro j
  exact ⟨_,rfl⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
