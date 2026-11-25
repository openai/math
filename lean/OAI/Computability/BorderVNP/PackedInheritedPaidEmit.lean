import OAI.Computability.BorderVNP.PackedInheritedPaidPins
import OAI.Computability.BorderVNP.PackedInheritedBirthRaw

/-! # Shared relative-address emitter writes the actual paid birth history

The seed compiler receives the virtual endpoint columns before any relocation.
At each paid site the emitted rows and all address marks equal the permanent
local history used in the observation and field models.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.PaidSite

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open BankJoint InheritedProfile
open scoped Classical

variable {D m ne np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (s : S) (a : Fin e.count) (v : (e.net a).Site)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (position : e.Entry → ℕ)

local notation3 "G₀" => (output e p bin perm positive first q).layout
local notation3 "tag₀" => (Sum.inr (Sum.inr ⟨a,v⟩) : TemplateSite e)
local notation3 "ws" => PaidBox.widths (e.net a) v
local notation3 "cp₀" => Subtype.val (q s) a
local notation3 "start₀" => starts e p bin perm positive first q s a v edgeID portID
local notation3 "raw₀" => relativeRaw e p bin perm positive first q s edgeID portID
local notation3 "state₀" => physical e p bin perm positive first q s a v edgeID portID position

omit [NeZero D] in
/-- Work in the compiler is exactly the two input and staging blocks of the paid program. -/
theorem raw_work (j : ℕ) (hist : Fin e.count → ℕ) :
    intrinsicWork e j hist tag₀ = work ws (hist a) := by
  change 2*(∑ r,ws r)*hist a = hist a*(∑ r,ws r)+hist a*(∑ r,ws r)
  ring

/-- Each genuine intrinsic seed operand is the actual base of the paid-site cable in its finite bank. -/
theorem raw_base (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v))) :
    raw₀ (.inr ⟨tag₀,some (some r)⟩) = work ws cp₀ + start₀ r := by
  obtain ⟨u,side,href,hs⟩ := referenced_start e p bin perm positive first q s a v edgeID portID r
  rw [relative_raw_ref e p bin perm positive first q s edgeID portID tag₀ r u side href,raw_work]
  exact congrArg (work ws cp₀ + ·) hs

/-- The new paid-site rows installed in the attained history are the actual output
of the common public seed-packet encoder, including every private staging and bundle tie. -/
theorem relative_emitted :
    emitted e first raw₀ tag₀ = (state₀).rows :=
  emitted_rows e p bin perm positive first q s a v edgeID portID position raw₀ rfl rfl rfl
    (raw_base e p bin perm positive first q s a v edgeID portID)

/-- Its persistent address/ID relocation marks are emitted in precisely the recorded order. -/
theorem relative_marks :
    ((rows e first tag₀).flatMap markedCode).map
      (fun z => (z.1,z.2.eval (fun i => word e raw₀ (pin e tag₀ i)))) = (state₀).markedWords :=
  emitted_marks e p bin perm positive first q s a v edgeID portID position raw₀
    (relative_emitted e p bin perm positive first q s a v edgeID portID position)

end Packing.Inherited.PaidSite

end BorderVNP
end Computability
end OAI
