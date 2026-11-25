import OAI.Hierarchy.DescentColonyReindex
import OAI.Hierarchy.DescentAffineColors
import OAI.Hierarchy.DescentColonyWinningSlabs
import OAI.Hierarchy.DescentSparseStep

namespace OAI
/-! # Identifying the native paint objective on the actual old graph -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentWalshTables
open scoped Classical BigOperators
noncomputable section

variable {k H d : ℕ} {V : Type} [Fintype V] [DecidableEq V] {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (core : Finset N.Edge) (e : V ≃ Fin H) (pos : N.Site→V)
variable (block : N.Site→Block k) (full : N.Site→ℕ) (near : V→Finset V) (D a B unit : ℕ)
local notation "load" => blockMass N pos block full
variable (small : ∀ (v : V) (x : Block k), blockMass N pos block full v x ≤ unit*B)
local notation "home" => occupiedHome N pos block full near D a (unit*B) small
local notation "Col" => occupied N (unit*B) near D a load small pos block
local notation "spatial" => occupiedAddress N (unit*B) near D a load small pos block
local notation "pay" => live (nativeTraffic N core home)
local notation "addr" => (fun u => Equiv.symm (address k) (block u))

private def name (s : WinningSlabs.Slot 1 H k) : V×(ℕ×ℕ) :=
  let t := (WinningSlabs.directory 1 H k).symm s
  (e.symm t.1.2,WinningSlabs.keyName k t.2)

omit [Fintype V] [DecidableEq V] in
private theorem name_inj : Function.Injective (name e (k:=k)) := by
  intro s t h
  apply (WinningSlabs.directory 1 H k).symm.injective
  exact Prod.ext (Prod.ext (Subsingleton.elim _ _) (e.symm.injective (congrArg Prod.fst h)))
    (WinningSlabs.name_injective (congrArg Prod.snd h))

omit [Fintype V] in
private theorem name_exists (c : Col) : ∃ i : WinningSlabs.Slot 1 H k, name e i=spatial c := by
  obtain ⟨u,uc⟩ := colonyOf_surjective N (unit*B) near D a load small pos block c
  let z := depthAt (unit*B) near D a load small (pos u) (block u)
  have hz : z≤k := (depth_le ..).trans (Nat.sub_le ..)
  let key : ℕ×ℕ := (z,group z (block u))
  have inList : key∈WinningSlabs.keys k :=
    (WinningSlabs.mem_keys k _ _).mpr ⟨hz,DescentHostDirectory.group_lt hz _⟩
  let j : Fin (WinningSlabs.keys k).length :=
    ⟨(WinningSlabs.keys k).idxOf key,List.idxOf_lt_length_iff.mpr inList⟩
  have read : WinningSlabs.keyName k j.val=key := by
    simp only [WinningSlabs.keyName,dite_eq_left j.isLt]
    exact List.idxOf_get (a:=key) (l:=WinningSlabs.keys k) j.isLt
  refine ⟨WinningSlabs.directory 1 H k ((0,e (pos u)),j),?_⟩
  rw [←uc,occupiedAddress_colonyOf]
  simp only [name,Equiv.symm_apply_apply,read]
  rfl

private def slot : Col ↪ WinningSlabs.Slot 1 H k :=
  ⟨fun c=>(name_exists N e pos block full near D a B unit small c).choose,fun c t h=>
    (spatial).injective (((name_exists N e pos block full near D a B unit small c).choose_spec).symm.trans
      ((congrArg (name e) h).trans (name_exists N e pos block full near D a B unit small t).choose_spec))⟩

variable (incoming : V→List V) (incoming_spec : ∀u v,u∈incoming v ↔ v∈near u)
variable (hD : 0<D)
include incoming_spec hD
local notation "rows" => Scan.build (fun t => List.map e (incoming (e.symm t)))
  (fun t=>load (e.symm t)) D (2^a*(unit*B)) k
local notation "A" => WinningSlabs.worldValue (fun _ : Fin 1=>rows) (fun _ t=>blockMass N pos block pay (e.symm t))

/-- One literal dense word sums the old outgoing weights at exactly one
physical block and one actual occupied vertex class. -/
private theorem word (s : WinningSlabs.Slot 1 H k) (x : Block k) :
    A s x=∑u, if spatial (home u)=name e s ∧ block u=x then pay u else 0 := by
  let t := (WinningSlabs.directory 1 H k).symm s
  let v := e.symm t.1.2
  let key := WinningSlabs.keyName k t.2
  let level := depthAt (unit*B) near D a load small v x
  let yes := level=key.1 ∧ group key.1 x=key.2
  have depth := Scan.leafDepth_eq incoming (fun u v=>v∈near u) incoming_spec load hD a (unit*B) small v x
  have depth' : Scan.leafDepth rows t.1.2 x=level := by
    have rename : Scan.leafDepth rows (e v) x=Scan.leafDepth (Scan.build incoming load D (2^a*(unit*B)) k) v x := by
      unfold Scan.leafDepth
      simp_rw [Scan.lookup_reindex e incoming load D (2^a*(unit*B))]
    simpa only [v,Equiv.apply_symm_apply] using rename.trans depth
  change (if WinningSlabs.member rows t.1.2 key.1 key.2 x then blockMass N pos block pay v x else 0)=_
  have active : WinningSlabs.member rows t.1.2 key.1 key.2 x ↔ yes := by
    unfold WinningSlabs.member
    rw [depth']
  have belong (u : N.Site) :
      spatial (home u)=name e s ∧ block u=x ↔ (pos u=v ∧ block u=x) ∧ yes := by
    rw [show spatial (home u)=colonyCode N (unit*B) near D a load small pos block u from occupiedAddress_colonyOf ..]
    change (pos u,depthAt (unit*B) near D a load small (pos u) (block u),
        group (depthAt (unit*B) near D a load small (pos u) (block u)) (block u))=(v,key) ∧ block u=x ↔ _
    constructor
    · rintro ⟨eqn,bx⟩
      have pv := congrArg Prod.fst eqn
      have d := congrArg (fun t : V×(ℕ×ℕ)=>t.2.1) eqn
      have q := congrArg (fun t : V×(ℕ×ℕ)=>t.2.2) eqn
      change pos u=v at pv
      change depthAt (unit*B) near D a load small (pos u) (block u)=key.1 at d
      change group _ (block u)=key.2 at q
      rw [pv,bx] at d q
      exact ⟨⟨pv,bx⟩,d,by rwa [d] at q⟩
    · rintro ⟨⟨pv,bx⟩,dv,qx⟩
      rw [pv,bx]
      exact ⟨Prod.ext rfl (Prod.ext dv (by change group level x=key.2; rwa [dv])),rfl⟩
  by_cases inside : yes
  · rw [ite_eq_left (active.mpr inside)]
    unfold blockMass
    apply Finset.sum_congr rfl
    intro u _
    apply if_congr _ rfl rfl
    exact ⟨fun h => (belong u).mpr ⟨h,inside⟩,fun h => ((belong u).mp h).1⟩
  · rw [ite_eq_right (fun h=>inside (active.mp h))]
    symm
    apply Finset.sum_eq_zero
    intro u _
    exact ite_eq_right (fun h => inside ((belong u).mp h).2)

/-- Each old cable is counted once in the physical paint score's capacity
bound. In particular the full public directory contributes no padding mass. -/
theorem directory_mass_named : (∑s,∑x,A s x)=core.card := by
  classical
  simp_rw [word N core e pos block full near D a B unit small incoming incoming_spec hD]
  calc
    _ = ∑s : WinningSlabs.Slot 1 H k, ∑u : N.Site, ∑x : Block k,
        if spatial (home u)=name e s ∧ block u=x then pay u else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑u : N.Site, ∑s : WinningSlabs.Slot 1 H k, ∑x : Block k,
        if spatial (home u)=name e s ∧ block u=x then pay u else 0 := Finset.sum_comm
    _ = ∑u,pay u := by
      apply Finset.sum_congr rfl
      intro u _
      let c := slot N e pos block full near D a B unit small (home u)
      have ix : name e c=spatial (home u) := (name_exists N e pos block full near D a B unit small (home u)).choose_spec
      have test (s : WinningSlabs.Slot 1 H k) : spatial (home u)=name e s ↔ s=c := by
        rw [←ix]
        exact ⟨fun h=>name_inj e h.symm,fun h=>congrArg (name e) h.symm⟩
      simp_rw [test]
      simp [ite_and]
    _ = core.card := live_is_core N core home

local notation "placed" => slot N e pos block full near D a B unit small
local notation "loads" => fun c : Col => slab pay addr (groupStream home c)

private theorem occupied_rows :
    (∀ c i,A (placed c) (address k i)=loads c i) ∧
      (∀ s,s∉Set.range placed → ∀ i,A s i=0) := by
  constructor
  · intro c i
    rw [word N core e pos block full near D a B unit small incoming incoming_spec hD]
    have code : name e (placed c)=spatial c := (name_exists N e pos block full near D a B unit small c).choose_spec
    rw [code]
    dsimp only [slab]
    rw [filtered_amount]
    let atBlock (u : N.Site) := if decide (addr u=i) = true then pay u else 0
    refine Eq.trans ?_ (amount_groupStream atBlock (fun u : N.Site => home u) c).symm
    apply Finset.sum_congr rfl
    intro u _
    have eqc : spatial (home u)=spatial c ↔ home u=c := (spatial).injective.eq_iff
    have eqx : addr u=i ↔ block u=address k i := Equiv.symm_apply_eq ..
    simp only [atBlock,eqc,←eqx,decide_eq_true_eq,ite_and]
  · intro s outside i
    rw [word N core e pos block full near D a B unit small incoming incoming_spec hD]
    apply Finset.sum_eq_zero
    intro u _
    have diff : spatial (home u)≠name e s := by
      intro eqn
      apply outside
      refine ⟨home u,name_inj e ?_⟩
      exact ((name_exists N e pos block full near D a B unit small (home u)).choose_spec).trans eqn
    exact ite_eq_right (fun both => diff both.1)

/-- Dense numerical and occupied-colony scores agree candidate by candidate, including ties. -/
theorem native_score_eq_named (j : DescentAffineColors.Candidate k) :
    DescentAffineColors.score A j = DescentAffineColors.score
      (fun t x=>loads ((Fintype.equivFin Col).symm t) ((address k).symm x)) j := by
  obtain ⟨row,off⟩ := occupied_rows N core e pos block full near D a B unit small incoming incoming_spec hD
  exact DescentAffineColors.score_on_directory A placed loads row off j

/-- The physical first minimum supplies the very affine balance used by the
sparse old-graph matching invoice, measured against occupied classes only. -/
theorem chosen_affine_balance_named (hu : 0<unit) (covered : ∀u,unit*pay u≤full u)
    (j : DescentAffineColors.Candidate k)
    (best : ∀b,DescentAffineColors.score A j≤DescentAffineColors.score A b) :
    affineBalance N core pos block full near D a B unit small
      (DescentAffineColors.linear j) (DescentAffineColors.offset j) := by
  obtain ⟨row,off⟩ := occupied_rows N core e pos block full near D a B unit small incoming incoming_spec hD
  exact DescentAffineColors.occupied_bound A placed loads row off B
    (actual_slab_cap N core pos block full near D a B unit small hu covered) j best

end

noncomputable section
variable {k H d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (core : Finset N.Edge) (position : N.Site→Fin H)
variable (block : N.Site→Block k) (full : N.Site→ℕ) (around : Fin H→Finset (Fin H)) (D a B unit : ℕ)
variable (fit : ∀v x,blockMass N position block full v x≤unit*B)
variable (links : Fin H→List (Fin H)) (found : ∀u v,u∈links v ↔ v∈around u) (hD : 0<D)
include found hD
local notation "home₀" => occupiedHome N position block full around D a (unit*B) fit
local notation "pay₀" => live (nativeTraffic N core home₀)
local notation "rows₀" => Scan.build links (blockMass N position block full) D (2^a*(unit*B)) k
local notation "A₀" => WinningSlabs.worldValue (fun _ : Fin 1=>rows₀) (fun _=>blockMass N position block pay₀)

/-- The Fin-addressed array has the same total mass as the old cable set. -/
theorem directory_mass : (∑s,∑x,A₀ s x)=core.card := by
  simpa using directory_mass_named N core (Equiv.refl _) position block full around D a B unit fit links found hD

/-- Native painting with Fin-addressed old sites. -/
theorem chosen_affine_balance
    (hu : 0<unit) (covered : ∀u,unit*pay₀ u≤full u) (j : DescentAffineColors.Candidate k)
    (best : ∀b,DescentAffineColors.score A₀ j≤DescentAffineColors.score A₀ b) :
    affineBalance N core position block full around D a B unit fit
      (DescentAffineColors.linear j) (DescentAffineColors.offset j) := by
  apply chosen_affine_balance_named N core (Equiv.refl _) position block full around D a B unit fit links found hD hu covered j
  simpa using best


end
end Hierarchy.DescentSixParty.StarKeys

end OAI
