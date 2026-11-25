import OAI.Hierarchy.DescentResetStemHalo
import OAI.Hierarchy.DescentGenuineRosterDistinct

namespace OAI
/-! The actual sparse and compact reset IDs and the earlier measured host roster. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentCommonHost
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentColonies.DynamicSplit
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph r Ht
local notation "used" => Fintype.card B.next.V
variable {H0 : ℕ} (previous : Fintype.card input.V≤H0)
local notation "hosts" => input.vertex.trans (Fin.castLEEmb previous)
local notation "adj" => hostRotor hosts (hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "real" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "rawSize" => H0*(pal).card

def compactActorOrder : B.next.V≃Fin used :=
  Equiv.ofBijective dense ((Fintype.bijective_iff_injective_and_card dense).mpr ⟨(dense).injective,by simp⟩)
def compactActorName (i : Fin used) : Fin rawSize:=real ((compactActorOrder B previous).symm i)

theorem compact_host_fields (v : B.next.V) :
    (real v).val%(pal).card=(((Z).rawHostRank T vertex) v).val%(pal).card ∧
    (real v).val/(pal).card=(oldRank (position (Z).graph v.val)).val:=by
  constructor
  · rfl
  · let z:=(Z).hostFields T oldRank v
    have fit:=z.2.isLt
    have pos : 0<(pal).card:=lt_of_le_of_lt (Nat.zero_le _) fit
    change (z.2.val+(pal).card*z.1.val)/(pal).card=z.1.val
    rw [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt fit,Nat.zero_add]

theorem old_roster (x y : Fin H0) : y∈(List.ofFn (adj x)).filterMap id ↔ ∃v u:input.V,x=hosts v ∧ y=hosts u ∧ v∈(A).near u:=by
  have any : y∈(List.ofFn (adj x)).filterMap id ↔ ∃j,adj x j=some y:=by simp [List.mem_filterMap,List.mem_ofFn,eq_comm]
  rw [any]
  constructor
  · rintro ⟨j,read⟩
    unfold hostRotor at read
    split at read
    next present=>
      obtain ⟨b,atB,atY⟩:=Option.map_eq_some_iff.mp read
      exact ⟨present.choose,b,present.choose_spec.symm,atY.symm,((A).symmetric _ _).mp ((hostRoster_mem A _ _ _).2 ⟨j,atB⟩)⟩
    next=>contradiction
  · rintro ⟨v,u,rfl,rfl,near⟩
    obtain ⟨j,hit⟩:=(hostRoster_mem A _ _ _).1 (((A).symmetric _ _).mp near)
    have present : ∃a,hosts a=hosts v:=⟨v,rfl⟩
    exact ⟨j,by rw [hostRotor,dite_eq_left present,(hosts).injective present.choose_spec,hit];rfl⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
