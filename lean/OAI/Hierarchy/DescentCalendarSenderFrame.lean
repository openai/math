import OAI.Hierarchy.DescentContactSenderRead

namespace OAI
/-! # A sender keeps the predecessor board across installations above it -/
namespace Hierarchy.DescentContactSenderDate
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetReciprocalPeer
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L L' cap n r b Ht w H G M : ℕ}
local notation "fields" a => DescentOldContactSender.count D a cap n r
local notation "vals" a => Fin H→Fin G→Fin (fields a)→Cell b
local notation "raw" a => Fin a→Fin (2*cap)→Fin H→Fin G→Cell b

def Prior.castLow (eqn : L=L') (u : Prior D L cap n r) : Prior D L' cap n r := eqn ▸ u

def Prior.castValues (eqn : L=L') (xs : vals L) : vals L' :=
  fun v g j=>xs v g (j.cast (congrArg (fun z=>fields z) eqn.symm))

def Prior.castRaw (eqn : L=L') (xs : raw L) : raw L' :=
  fun lo=>xs (lo.cast eqn.symm)

theorem Prior.castLow_heq (eqn : L=L') (u : Prior D L cap n r) : HEq (u.castLow eqn) u := by subst L'; rfl

theorem Prior.castLow_decode (eqn : L=L') (xs : vals L) (v : Fin H) (g : Fin G) :
    HEq (DescentOldContactSender.decode (Prior.castValues eqn xs v g)) (DescentOldContactSender.decode (xs v g)) := by
  subst L'; rfl

variable (u : Prior D L cap n r) (xs : Fin H→Fin G→Fin (DescentOldContactSender.count D L cap n r)→Cell b)
  (next : Adj H D) (words : Fin L→Fin (2*cap)→Fin H→Fin G→Cell b)
variable (first after : ℕ)
local notation "a₀" => (Layout.mk first H G M : Layout D L cap n r Ht b)
local notation "a₁" => (Layout.mk after H G M : Layout D L' cap n r Ht b)

/-- The same hardware terms continue reading the same previous data when only the
low-axis numeral changes by the supplied equality. -/
theorem Prior.rebase (eqn : L=L') (mem out : Memory w) (fit : (a₀).PriorFits u w)
    {bank : Bank} (roster : Accessible u.routes bank H G M w first)
    (live : (a₀).Before u xs next words mem) (frame : ∀a,a < first → out a=mem a) :
    (a₁).Before (u.castLow eqn) (Prior.castValues eqn xs) next (Prior.castRaw eqn words) out := by
  subst L'
  refine ⟨?_,(a₀).old_routes u roster live.ports frame,?_,?_,?_⟩
  · intro j p
    exact (eval_below _ _ mem out (fit.board j) frame).trans (live.input j p)
  · intro lo j p
    have span:=(fit.route lo j).srcRoom
    have low:=(fit.route lo j).source.2.2
    have point:=(Nat.add_lt_add_left ((row H G M p).isLt.trans_le span) _).trans_le low
    exact (frame _ point).trans (live.signed lo j p)
  · intro p
    exact (eval_below _ _ mem out fit.host frame).trans (live.host p)
  · intro p
    exact (eval_below _ _ mem out fit.ones frame).trans (live.ones p)

end
end Hierarchy.DescentContactSenderDate

end OAI
