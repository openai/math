import OAI.Hierarchy.DescentOccupiedGain

namespace OAI
/-! # Independently scaled geometric marks, bundle counts, and paid local width -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentHostDegree GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {n k : ℕ} {P : Type*} {bits : P→ℕ}
    (N : Network n P bits) (pos : N.Site→V) (block : N.Site→Block k) (full : N.Site→ℕ)
    (near : V→Finset V) (a₀ Δ markCap pairCap : ℕ)
variable (small : ∀ (v : V) (x : Block k), blockMass N pos block full v x ≤ markCap)
private abbrev scaledHome := occupiedHome N pos block full near (gap Δ) (packExponent a₀ Δ) markCap small
local notation "A" => packExponent a₀ Δ
local notation "D" => gap Δ
local notation "load" => blockMass N pos block full
local notation "home" => scaledHome N pos block full near a₀ Δ markCap small
local notation "Col" => occupied N markCap near (gap Δ) (packExponent a₀ Δ) (blockMass N pos block full) small pos block
local notation "col" => occupiedAddress N markCap near (gap Δ) (packExponent a₀ Δ) (blockMass N pos block full) small pos block
variable (core : Finset N.Edge) (sheet : Block k→Bool)
local notation "paint" => (sheet ∘ block)
local notation "pack" => coloredPack N core (scaledHome N pos block full near a₀ Δ markCap small) (sheet ∘ block) pairCap
local notation "pick" => colorPick N core (scaledHome N pos block full near a₀ Δ markCap small) (sheet ∘ block) pairCap
local notation "Pairs" => NativePair N core (scaledHome N pos block full near a₀ Δ markCap small) (sheet ∘ block) pairCap

omit [Fintype V] in
/-- The mark scale and the packer's count scale cancel after bounding the
real selected outgoing count in a first-unsplit physical colony. -/
theorem scaled_pair_cap (unitMass : ℕ) (positive : 0<unitMass) (scales : markCap=unitMass*pairCap)
    (enough : ∀u,unitMass*live (nativeTraffic N core home) u≤full u) (c : Col) :
    amount (live (nativeTraffic N core home)) (thinList home paint c)≤2^A*pairCap := by
  apply Nat.le_of_mul_le_mul_left (c := unitMass) _ positive
  have h := (scaled_thin_le_fiber N core home paint full unitMass enough c).trans
    (occupied_mass N pos block full near D A markCap small c)
  apply h.trans_eq
  rw [scales]
  ring

omit [Fintype V] in
/-- The entire old-site fiber at a genuine new star, including memory and
coefficient payload in the old full charges. -/
theorem scaled_occupied_old_fiber (l : Bool)
    (positive : 0<pairCap) (unitMass wireScale : ℕ) (unitPos : 0<unitMass)
    (scales : markCap=unitMass*pairCap) (paidEdge : ∀e∈core,unitMass≤wireScale*N.width e)
    (carried : N.Site→ℕ) (pays : ∀u,wireScale*siteLoad N u+carried u≤full u)
    (degree : ∀v,(near v).card≤Δ)
    (adj : ∀e∈core,pos (N.dst e)∈near (pos (N.src e)) ∧ pos (N.src e)∈near (pos (N.dst e)))
    (sameBlock : ∀e∈core,block (N.src e)=block (N.dst e)) (v : Merged N pick l pack) :
    10*(∑u : {u : N.Site // newSite N pick l pack (.inl u)=v},full u.val)≤2^gainExponent a₀ Δ*markCap := by
  let allow : Col → Finset Col := oneNeighbor near D col
  let atV := fun (u : N.Site)=>newSite N pick l pack (.inl u)=v
  let Fiber := {u : N.Site // atV u}
  have colors (e) (he : e∈core) : paint (N.src e)=paint (N.dst e) := congrArg sheet (sameBlock e he)
  let chosen := starLabel N core home paint pairCap colors l v
  let rosterV := roster N core home paint pairCap allow chosen
  have old (e) (he : e∈core) : home (N.src e)∈allow (home (N.dst e)) :=
    actual_neighbor N markCap near D A load small pos block (adj e he).2 (adj e he).1 (sameBlock e he)
  have smallSource (c) : (allow c).card ≤ allowedSources Δ :=
    (oneNeighbor_card near D Δ col degree c).trans (Nat.le_add_left _ _)
  have enough (u) : unitMass*live (nativeTraffic N core home) u≤full u :=
    (scaled_outgoing_le N core home unitMass wireScale paidEdge u).trans ((Nat.le_add_right _ (carried u)).trans (pays u))
  have thin := scaled_pair_cap N pos block full near a₀ Δ markCap pairCap small core sheet unitMass unitPos scales enough
  have count : rosterV.card≤1+allowedSources Δ*(2^A+1) :=
    roster_card N core home paint pairCap allow _ _ positive smallSource thin chosen
  have covered := roster_covers N core home paint pairCap allow colors l (oneNeighbor_self near D col) old v
  have mass (q : NativePack N core home paint pairCap) :
      (∑ u ∈ Finset.univ.filter (fun u : N.Site => pack u = q), full u) ≤ 2^A*markCap := by
    apply le_trans _ (occupied_mass N pos block full near D A markCap small (packColony q))
    apply Finset.sum_le_sum_of_subset
    intro u hu
    have eqn := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (pack_home N pairCap home paint core u).symm.trans
      (congrArg packColony eqn)⟩
  have totals : (∑ u : Fiber, full u.val) ≤ rosterV.card*(2^A*markCap) := by
    apply fiber_load atV pack full rosterV _ covered
    intro q _
    simpa only [Finset.sum_filter] using mass q
  have all_ := totals.trans (Nat.mul_le_mul_right _ count)
  exact (Nat.mul_le_mul_left 10 all_).trans (gain_covers a₀ Δ markCap)

omit [Fintype V] in
/-- A branch-specific bit alphabet uses wireScale normalized units per bit.
The full mark includes carried memory. The geometric slot count is paid in
bundle units and the final full load in the independently scaled mark units. -/
theorem scaled_occupied_gain {F : Type*} [Field F] (G : PoweredGadget F) (l : Bool)
    (positive : 0<pairCap) (unitMass wireScale : ℕ) (unitPos : 0<unitMass)
    (scales : markCap=unitMass*pairCap) (paidEdge : ∀e∈core,unitMass≤wireScale*N.width e)
    (carried : N.Site→ℕ) (pays : ∀u,wireScale*siteLoad N u+carried u≤full u)
    (degree : ∀v,(near v).card≤Δ)
    (adj : ∀e∈core,pos (N.dst e)∈near (pos (N.src e)) ∧ pos (N.src e)∈near (pos (N.dst e)))
    (sameBlock : ∀e∈core,block (N.src e)=block (N.dst e)) (z : Pairs→ℕ) (p : Pairs→Profile G.C)
    (fit : ∀i s,N.width (pick (i,s))=z i*G.b) {d : ℕ}
    (position : Merged N pick l pack→EuclideanSpace ℝ (Fin d)) (ball : ∀q,‖position q‖≤1)
    (v : Merged N pick l pack) :
    let w : Pairs → Fin 8 → ℕ := fun i e => z i * (((p i).1 e).val + G.k)
    2*(wireScale*siteLoad (merged N pick w l pack position ball) v+
      ∑u : {u : N.Site // newSite N pick l pack (.inl u)=v},carried u.val)≤2^gainExponent a₀ Δ*markCap := by
  dsimp only
  let Fiber := {u : N.Site // newSite N pick l pack (.inl u)=v}
  have oldCap := scaled_occupied_old_fiber N pos block full near a₀ Δ markCap pairCap small core sheet l
    positive unitMass wireScale unitPos scales paidEdge carried pays degree adj sameBlock v
  let oldW := ∑u : Fiber,siteLoad N u.val
  let info := ∑u : Fiber,carried u.val
  have pay : wireScale*oldW+info≤∑u : Fiber,full u.val := by
    dsimp only [oldW,info]
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun u _=>pays u.val
  let w : Pairs → Fin 8 → ℕ := fun i e => z i * (((p i).1 e).val + G.k)
  have wBound : siteLoad (merged N pick w l pack position ball) v≤5*oldW :=
    merged_site_load_five N pick l pack position ball v G z p fit
  have scaled : wireScale*siteLoad (merged N pick w l pack position ball) v≤5*(wireScale*oldW) := by
    simpa only [Nat.mul_left_comm wireScale] using Nat.mul_le_mul_left wireScale wBound
  have one : wireScale*siteLoad (merged N pick w l pack position ball) v+info ≤5*(wireScale*oldW+info) := by omega
  calc
    _ ≤2*(5*(wireScale*oldW+info)) := Nat.mul_le_mul_left 2 one
    _ ≤2*(5*(∑u : Fiber,full u.val)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 5 pay)
    _ =10*(∑u : Fiber,full u.val) := by ring
    _ ≤_ := oldCap

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
