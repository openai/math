import OAI.Hierarchy.DescentResetParentOriginHosts
import OAI.Hierarchy.DescentContactCoordinateJoint

namespace OAI
/-! The joint of a current site shape and a strictly positive prior halo ordinal. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentContactCoordinateJoint
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "rad" => 2^(Nat.clog 2 ((A).degree+2))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

def jointNumber (u : Host) (a : (Z).V) (shape : ℕ) :=number rad shape (haloNumber B u a+1)

theorem halo_radix (u : Host) (v : (Z).V) (member_ : v∈originDomain B u) :
    haloNumber B u v+1<rad:=by
  let table:=haloNumbers B u
  let code:=(T).columns.host v
  have member : code∈table:=Finset.mem_image_of_mem _ member_
  have less : (table.filter (·<code))⊂table:=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨code,member,by simp⟩
  have short : haloNumber B u v<(A).degree+1:=
    (Finset.card_lt_card less).trans_le (Finset.card_image_le.trans (origin_domain_room B u))
  exact (Nat.succ_lt_succ short).trans_le (Nat.le_pow_clog (by decide) _)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
