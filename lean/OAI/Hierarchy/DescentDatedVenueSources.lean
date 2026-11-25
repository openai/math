import OAI.Hierarchy.DescentGroupHostOrdinal
import OAI.Hierarchy.DescentPackedActorRaster
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPackedCensusPorts
import OAI.Hierarchy.DescentReachedCensusCount

namespace OAI
/-! # Original physical actor, signed cable, hub and history fields of a dated stage -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSIMDLookup DescentStageEdgeReceipt
open scoped Classical Fin.CommRing
noncomputable section
section
variable {J V : Type}

/-- Append the public old-block digit to an immutable host ordinal. -/
def cableNames (k : ℕ) (rank : (J×V)↪ℕ) : DescentSharedCableNames.Stage.Host J V k↪ℕ where
  toFun x:=rank x.1*2^k+x.2.val
  inj' := by
    rintro ⟨h,x⟩ ⟨v,y⟩ eqn
    have pos := Nat.two_pow_pos k
    change rank h*2^k+x.val=rank v*2^k+y.val at eqn
    have hi := congrArg (·/2^k) eqn
    have lo := congrArg (·%2^k) eqn
    change (rank h*2^k+x.val)/2^k=(rank v*2^k+y.val)/2^k at hi
    rw [Nat.mul_comm (rank h),Nat.mul_comm (rank v),Nat.mul_add_div pos,Nat.mul_add_div pos,
      Nat.div_eq_of_lt x.isLt,Nat.div_eq_of_lt y.isLt,Nat.add_zero,Nat.add_zero] at hi
    simp only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] at lo
    exact Prod.ext (rank.injective hi) (Fin.ext lo)

end

namespace Prepare
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i a s M H G w : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {T : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W T price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J↪Fin G) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)

def spreadField {X : Type*} (zero : X) (f : J×V→X) (h : Fin H) (g : Fin G) : X :=
  if live : ∃z : J×V,groups z.1=g ∧ hosts z.2=h then f live.choose else zero

def actors := spreadField groups hosts 0 (DescentActorRaster.actorMask A.pos A.block)
def winners (x : Fin (2^k)) := spreadField groups hosts 0 (fun h=>win h x)
def signed (x : Fin (2^k)) (j : Fin (2*A.cap)) := spreadField groups hosts none
  (fun h=>DescentSharedCableNames.Stage.signedPanel A native S ready (cableNames k rank) (h,x) j)

end Prepare

namespace Census
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age G H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)

def hub (h : Fin H) : Cell 1 :=
  if v : ∃u,hosts u=h then if A.hub v.choose then 1 else 0 else 0

end Census

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
