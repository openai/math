import OAI.Hierarchy.DescentCommonBlockAddress
import OAI.Hierarchy.DescentReentryLoad

namespace OAI
/-! # Coarse coordinates, actor load, and saturated hubs in the new common host -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost DescentChosenRouter DescentRelativeContacts DescentColonies
open DescentResetAttachments DescentResetTrunks StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "R" => Z.placement
local notation "m" => T.commonDepth
local notation "lab" => fun t=>shortName m (T.code t)
local notation "view" => rawCoordinate (R) Z.graph m T.code Z.positive Z.pay Z.circuit d
local notation "eqWidth" => funext (fun i=>Eq.symm (Z.allWidths i))

def blockId (v : (W).graph.Site) : Block m :=
  ⟨view (resetNames Z T v),raw_lt (R) Z.graph m T.code T.commonLow T.codeLegal Z.positive Z.pay Z.circuit d _⟩

theorem block_edges (e : (W).graph.Edge) : blockId Z T ((W).graph.src e)=blockId Z T ((W).graph.dst e) := by
  apply Fin.ext
  apply read_common_incidence A T.home (R).input T.hub eqWidth Z.bank Z.tables view Eq _ _ _ e
  · intro s i
    have name := public_read (R) T.code T.source s i
    rw [←T.attach] at name
    exact (congrArg (coarseName m) name.symm).trans
      (public_coordinate (R) Z.graph m T.code Z.positive Z.pay Z.circuit d s ((R).input s i)).symm
  · intro z
    rfl
  · exact bank_coordinate (R) Z.graph m T.code Z.positive Z.pay Z.circuit d T.coarseLinks

theorem place_unique {v w : (W).graph.Site} (pos : placed Z T v=placed Z T w) (coarse : blockId Z T v=blockId Z T w) : v=w :=
  (resetNames Z T).injective (raw_recover (R) Z.graph m T.code T.codeLegal Z.positive Z.pay Z.circuit d
    (congrArg Fin.val coarse) (congrArg Subtype.val pos))

theorem common_site_count : Fintype.card (W).graph.Site≤Fintype.card ↥(commonNames Z T)*2^m := by
  let put (u : (W).graph.Site) := (placed Z T u,blockId Z T u)
  have inject : Function.Injective put := fun _ _ h=>place_unique Z T (congrArg Prod.fst h) (congrArg Prod.snd h)
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective put inject

theorem bank_birth_count {r : ℕ} (range : Z.k-m≤r) :
    Fintype.card Z.bank.Site ≤ (Fintype.card Z.V*(2^(resetHostGain h (2^Z.n) Ht)*2^r))*2^m := by
  let put (u : Z.bank.Site) := (resetNames Z T).symm (Sum.inr u)
  have inject : Function.Injective put := (resetNames Z T).symm.injective.comp Sum.inr_injective
  exact (Fintype.card_le_of_injective put inject).trans ((common_site_count Z T).trans
    (Nat.mul_le_mul_right _ (placed_growth Z T range)))

private def nodeTag {V J : Type} {Y : ℕ} : Node V (V × DescentContacts.Endpoint Y) J → Bool
  | .trunk false z => z.2.2.isNone
  | _ => false

def commonTag (x : ↥(commonNames Z T)) : Bool := nodeTag x.val

private theorem name_at (x : (Bool × Z.Fallback) ⊕ Z.bank.Site) :
    (placed Z T ((resetNames Z T).symm x)).val =
      rawName (R) Z.graph m T.code Z.positive Z.pay Z.circuit d x :=
  congrArg (rawName (R) Z.graph m T.code Z.positive Z.pay Z.circuit d)
    ((resetNames Z T).apply_symm_apply x)

open private Hierarchy.DescentResetTrunks.installedHub_read from OAI.Hierarchy.DescentReentryLoad in
private theorem tag_at_name (x : (Bool × Z.Fallback) ⊕ Z.bank.Site) :
    reentryTag Z T ((resetNames Z T).symm x) =
      (match x with | .inl (false,t) => T.hub t | _ => false) := by
  apply (Hierarchy.DescentResetTrunks.installedHub_read
    A T.home (R).input T.hub eqWidth Z.bank Z.tables x).trans
  rcases x with ⟨(_|_),t⟩|r <;> rfl

theorem placed_tag (v : (W).graph.Site) : commonTag Z T (placed Z T v)=reentryTag Z T v := by
  obtain ⟨x,rfl⟩ := (resetNames Z T).symm.surjective v
  unfold commonTag
  rw [tag_at_name,name_at]
  rcases x with ⟨s,t⟩|⟨⟨s,g|t⟩,cell⟩
  · cases s
    · have eqn := T.hubShape t
      change (T.code t).2.2.isNone = T.hub t
      cases hv : T.hub t <;> cases he : (T.code t).2.2 <;> simp_all
    · rfl
  · rfl
  · rfl

theorem hub_present (v : ↥(commonNames Z T)) (hub : commonTag Z T v=true) (c : Block m) :
    ∃u : (W).graph.Site,placed Z T u=v ∧ blockId Z T u=c := by
  obtain ⟨v,hv⟩ := v
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x,rfl⟩ := (resetNames Z T).symm.surjective u
  have tag := (placed_tag Z T ((resetNames Z T).symm x)).symm.trans hub
  rw [tag_at_name] at tag
  rcases x with ⟨(_|_),t⟩|hsite
  · obtain ⟨t',_,group,names⟩ := T.hubCover t tag c
    refine ⟨(resetNames Z T).symm (.inl (false,t')),Subtype.ext ?_,Fin.ext ?_⟩
    · have trunk (z : Z.Fallback) : (placed Z T ((resetNames Z T).symm (.inl (false,z)))).val =
          Node.trunk false (shortName m (T.code z)) := name_at Z T _
      exact (trunk t').trans ((congrArg (Node.trunk false) names).trans (trunk t).symm)
    · change view ((resetNames Z T) ((resetNames Z T).symm (.inl (false,t')))) = c.val
      rw [Equiv.apply_symm_apply]
      exact group
  · cases tag
  · cases tag

variable (full : (reenter Z T).graph.Site→ℕ)
theorem actual_mass (u : (W).graph.Site) :
    blockMass (W).graph (placed Z T) (blockId Z T) full (placed Z T u) (blockId Z T u)=full u := by
  unfold blockMass
  rw [Finset.sum_eq_single u]
  · simp
  · intro i _ ne
    exact ite_eq_right (fun hit=>ne (place_unique Z T hit.1 hit.2))
  · simp

theorem mass_cap {B : ℕ} (bounded : ∀u : (reenter Z T).graph.Site,full u≤B) (v : ↥(commonNames Z T)) (c : Block m) :
    blockMass (W).graph (placed Z T) (blockId Z T) full v c≤B := by
  by_cases live : ∃u,placed Z T u=v ∧ blockId Z T u=c
  · obtain ⟨u,rfl,rfl⟩ := live
    exact (actual_mass Z T full u).le.trans (bounded u)
  · unfold blockMass
    have absent (u : (W).graph.Site) : ¬(placed Z T u=v ∧ blockId Z T u=c) :=
      fun hit=>live ⟨u,hit⟩
    simp [absent]

theorem hub_mass {B : ℕ} (fullHub : ∀u,reentryTag Z T u=true→full u=B)
    (v : ↥(commonNames Z T)) (hub : commonTag Z T v=true) (c : Block m) :
    blockMass (W).graph (placed Z T) (blockId Z T) full v c=B := by
  obtain ⟨u,rfl,rfl⟩ := hub_present Z T v hub c
  exact (actual_mass Z T full u).trans (fullHub u ((placed_tag Z T u).symm.trans hub))

variable (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "cap" => 2^g*B
local notation "cost" => MarkedWorld.siteUnits (reenter Z T) (reentryTag Z T) (measuredRecords Z T old) wire 256 hist
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+DescentMixedRouter.rotorRate h C)*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (rows : 9*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (hubBound : 3*((2^g*B:ℕ):ℝ)/256+hist≤((2^g*B:ℕ):ℝ))

include bill rotor rows hubBound in
/-- Complete site and stored-history loads, at the same normalized position
and surviving block used by the actual graph incidences. -/
theorem physical_block_mass (v : ↥(commonNames Z T)) (c : Block m) :
    blockMass (W).graph (placed Z T) (blockId Z T) cost v c≤cap ∧
    (commonTag Z T v=true→blockMass (W).graph (placed Z T) (blockId Z T) cost v c=cap) := by
  have bounds := physical_site_units Z T old wire hist f g B bill rotor rows hubBound
  exact ⟨mass_cap Z T cost (fun u=>(bounds u).1) v c,
    fun hv=>hub_mass Z T cost (fun u=>(bounds u).2) v hv c⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
