import OAI.Hierarchy.DescentSparseBinTarget

namespace OAI
/-! # Padded first-fit receipts at the local slots physically emitted for the old graph -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM.Aperture
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM FirstFitRAM
open scoped Classical Fin.CommRing
variable {I C : Type*} [Fintype C] [DecidableEq C] {S : Finset C} {n w : ℕ}

def rowName (A : Aperture S n) (p : Fin n) : Option C :=
  A.target ((order A.key).symm (Sparse.position n p))

def mass (A : Aperture S n) (cap : C→ℕ) (p : Fin n) := ((A.rowName p).map cap).getD 0

theorem row_at (A : Aperture S n) (a : Fin (roster S).length) :
    A.rowName ((padded A.capacity).slot a)=some ((dense S).name a) := by
  let j := coordinate S a
  have eqn : order A.key (A.entry j)=Sparse.position n ((padded A.capacity).slot a) := by
    apply Fin.ext
    rw [A.entry_rank]
    simp [padded,padSlot,coordinate,position,j]
  unfold rowName
  rw [←eqn,Equiv.symm_apply_apply,A.covered]
  rfl

theorem row_padding (A : Aperture S n) (p : Fin n) (hp : p∈(padded A.capacity).padding) :
    A.rowName p=none := by
  apply A.nonentry
  intro a eqn
  have ord := A.entry_rank a
  rw [eqn,Equiv.apply_symm_apply] at ord
  let label := (coordinate S).symm a
  apply (padded A.capacity).apart p hp label
  apply (Sparse.position n).injective
  apply Fin.ext
  change (Sparse.position n (padSlot A.capacity label)).val=_
  simpa [padSlot,position,coordinate,label] using ord.symm

theorem mass_correct (A : Aperture S n) (cap : C→ℕ) :
    (padded A.capacity).Fits (cap ∘ (dense S).name) (A.mass cap) := by
  exact ⟨fun j=>by simp [mass,A.row_at],fun j hj=>by simp [mass,A.row_padding j hj]⟩

/-- This is the exact original use of a named destination at every stage;
adding the native shared-tape prefix yields its original thick-edge address. -/
theorem original_use (A : Aperture S n) (amount : I→ℕ) (xs : List I) (cap : C→ℕ)
    (support : ∀v,0<cap v→v∈keep S) (i : ℕ) (a : Fin (roster S).length) :
    assigned amount ((padded A.capacity).slot a) ((pack amount xs (A.mass cap)).decisions.take i)=
      assigned amount ((dense S).name a) ((pack amount xs cap).decisions.take i) := by
  let : Nonempty (Fin (roster S).length) := ⟨a⟩
  exact (padded A.capacity).full_prior (dense S) amount xs cap (A.mass cap) (A.mass_correct cap) support i a

/-- Decode the tag through the actual ranked name bank. The local and original
decision tapes have identical item names and targets, including all misses. -/
theorem original_decisions (A : Aperture S n) [Nonempty (Fin (roster S).length)] (amount : I→ℕ)
    (xs : List I) (cap : C→ℕ) (support : ∀v,0<cap v→v∈keep S) :
    ((pack amount xs (A.mass cap)).decisions.map (fun p=>(p.1,p.2.bind A.rowName)))=
      (pack amount xs cap).decisions := by
  rw [(padded A.capacity).decisions amount xs _ _ (A.mass_correct cap),List.map_map,←(dense S).decisions amount xs cap support]
  apply List.map_congr_left
  intro q _
  obtain ⟨i,_|a⟩ := q
  · rfl
  · simp [Expansion.put,Directory.decode,A.row_at]

/-- The old-edge issuer reads an actual numeric padded tag, not a supplied
choice. The decoded entire decision tape equals the original allocator's tape. -/
theorem native (A : Aperture S n) [Nonempty (Fin (roster S).length)] (amount : I→ℕ)
    (xs : List I) (cap : C→ℕ) (m : Memory w) (p : SelectionTrace.Layout)
    (sp : SelectionTrace.Room w (Fintype.card (Fin n)) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps (A.mass cap) m) (bound : ∀v,A.mass cap v<2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i<2^w) (j : Fin (pack amount xs (cap ∘ (dense S).name)).decisions.length) :
    SelectionTrace.final p (Fintype.card (Fin n)) m (p.tag j.val)=
      (binTag (((pack amount xs (cap ∘ (dense S).name)).decisions.get j).2.map (padded A.capacity).slot):Word w) :=
  (padded A.capacity).native_decisions amount xs _ (A.mass cap) (A.mass_correct cap) m p sp fits values bound input widths j

end Hierarchy.DescentPacking.SparseBinRAM.Aperture

end
end OAI
