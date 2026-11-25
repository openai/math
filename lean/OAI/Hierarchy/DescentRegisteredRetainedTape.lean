import OAI.Hierarchy.DescentRegisterInstructionRun
import OAI.Hierarchy.DescentPackedProfileShelfRoom

namespace OAI
/-! # The original packed ballot remains available below all register dates -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentPackedProfileTape ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ} {Cut : ℕ→Type*} (issue : ∀i,Cut i→Position→Move w→Prop)
    (initial : Position) (header : ℕ)
local notation "cursor" => position issue initial
local notation "cpu" => date issue initial
variable (protected_ : ∀i,Protected (date issue initial i) (position issue initial i).floor header)

theorem initial_below_cursor (i : ℕ) : initial.floor≤(cursor i).floor:=by
  rw [position_floor]
  exact floor_mono _ _ (show 0≤ i from Nat.zero_le _)

include protected_ in
theorem kept_original (m : Memory w) (j : ℕ) (before : j < initial.floor) (away : j≠header) (i : ℕ) :
    DateCode.history cpu m i j=m j:=by
  induction i with
  | zero=>rfl
  | succ i prev=>
    obtain ⟨out,run,keep⟩:=(protected_ i).run (DateCode.history cpu m i)
    have same : DateCode.history cpu m (i+1)=out:=(cpu i).nextMemory_eq run
    exact (congrFun same j).trans ((keep j (before.trans_le (initial_below_cursor issue initial i)) away).trans prev)

variable {A:Type} {pitch lo i:ℕ} {entries:List (Source A)}
include protected_ in
theorem retained_tape (s : DescentPackedEpochShelves.Shelf A) (stored : s∈shelves pitch lo 0 entries)
    (below : lo+extent pitch entries≤header) (allocated : header < initial.floor) (space : (cursor i).floor<2^w)
    (votes : A→Bool) (m : Memory w) (tape : ∀j : Fin (slots s.src.seats pitch),
      m (s.base+j.val)=((packed s.src.pin votes pitch j.val).val:Word w)) :
    (sourceBank s.base s.src.seats pitch).Fits w (cursor i).floor ∧
    ∀j : Fin (slots s.src.seats pitch),DateCode.history cpu m i (s.base+j.val)=
      ((packed s.src.pin votes pitch j.val).val:Word w):=by
  have here:=initial_below_cursor issue initial i
  refine ⟨shelf_fits s stored (below.trans (allocated.le.trans here)) space,?_⟩
  intro j
  have b:=(placed pitch lo 0 entries s stored).2
  change s.base+2*DescentDyadicSpan.span (slots s.src.seats pitch)≤lo+extent pitch entries at b
  have rows:=DescentDyadicSpan.span_ge (slots s.src.seats pitch)
  have index:=j.isLt
  have early : s.base+j.val<header:=by omega
  exact (kept_original issue initial header protected_ m _ (early.trans allocated) early.ne i).trans (tape j)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
