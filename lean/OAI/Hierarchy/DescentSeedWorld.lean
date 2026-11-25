import OAI.Hierarchy.DescentNativeInput
import OAI.Hierarchy.DescentSeedGeometry
import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # Physical seed placement, with one ordinary history atom and a charged tether per hub -/

namespace Hierarchy.DescentInitialHost
open DescentSixParty StarKeys Computability.BorderVNP.Crossing Catalyst CatalystSubstitution CorrectionBatch
open DescentColonies
open scoped BigOperators Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable {R s : ℕ} (c : (initialGroup X R s).Choice)
local notation "W" => (initialGroup X R s).state c
local notation "N" => X.network.copyGraph

def seedHub (u : (W).graph.Site) : Bool := hubFlag N u.2
/-- A marker is retained only for a genuine internal census. The selector
itself is the actual local history symbol, chosen in this very branch. -/
def seedRecords (u : (W).graph.Site) :
    List (Σv : (N).Site,Count (markedInput X).graph s (.inl v)) :=
  match u with
  | ⟨j,.inl v⟩=>[⟨v,c j (.inl v)⟩]
  | ⟨_,.inr _⟩=>[]

variable {G : Type} [Fintype G] [DecidableEq G] {l : ℕ} (digits : Fin R≃G×Block l)
def seedPos (u : (W).graph.Site) : G×Site N := ((digits u.1).1,u.2)
def seedBlock (u : (W).graph.Site) : Block l := (digits u.1).2

omit [Fintype G] [DecidableEq G] in
theorem seed_coordinates : Function.Injective (fun u : (W).graph.Site=>(seedPos X c digits u,seedBlock X c digits u)) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ eqn
  have hi : (digits i).1=(digits j).1 := congrArg (fun t : (G×Site N)×Block l => t.1.1) eqn
  have lo : (digits i).2=(digits j).2 := congrArg (fun t : (G×Site N)×Block l => t.2) eqn
  have base : i=j := digits.injective (Prod.ext hi lo)
  subst j
  have name : u=v := congrArg (fun t=>t.1.2) eqn
  subst v
  rfl

theorem measure_seed (wire hist : ℕ) (u : (W).graph.Site) :
    (W).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist u=
      incidenceLoad N (wire*s) 256 u.2+(if hubFlag N u.2 then 0 else hist) := by
  rcases u with ⟨j,v⟩
  let w (e : Wire N) := ((hubbed N).width e)
  have one (e : Wire N) : w e=1 := hub_unit N (physical_output X).1 e
  have split (t : Wire N→Site N) :
      (∑ e : Σ _ : Fin R,Wire N,if (⟨j,v⟩ : Σ _ : Fin R,Site N)=⟨e.1,t e.2⟩
        then wire*(s*w e.2)*(if hubFlag N (t e.2) then 256 else 1) else 0)=
        ∑e : Wire N, if v=t e then (wire*s)*(if hubFlag N (t e) then 256 else 1) else 0 := by
    rw [Fintype.sum_sigma,Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
    · apply Finset.sum_congr rfl
      intro e _
      have same : ((⟨j,v⟩ : Σ _ : Fin R, Site N)=⟨j,t e⟩) ↔ v=t e :=
        ⟨congrArg (fun a : Σ _ : Fin R, Site N => a.2),
          congrArg (fun z : Site N => (⟨j,z⟩ : Σ _ : Fin R, Site N))⟩
      simp only [same,one,Nat.mul_one]
    · intro i _ different
      apply Finset.sum_eq_zero
      intro e _
      exact ite_eq_right (fun h=>different (congrArg Sigma.fst h).symm)
  have physical (endpt : (W).graph.Edge → (W).graph.Site) (t : Wire N → Site N)
      (edge : ∀ e, endpt e=⟨e.1,t e.2⟩) :
      (∑ e : (W).graph.Edge, if (⟨j,v⟩ : (W).graph.Site)=endpt e then
        wire*(W).graph.width e*(if seedHub X c (endpt e) then 256 else 1) else 0)=
      ∑ e : Wire N, if v=t e then (wire*s)*(if hubFlag N (t e) then 256 else 1) else 0 := by
    refine Eq.trans ?_ (split t)
    apply Finset.sum_congr rfl
    intro e _
    by_cases hit : (⟨j,v⟩ : (W).graph.Site)=endpt e
    · have localHit : (⟨j,v⟩ : Σ _ : Fin R, Site N)=⟨e.1,t e.2⟩ := hit.trans (edge e)
      rw [ite_eq_left hit,ite_eq_left localHit,edge e]
      rfl
    · have miss : (⟨j,v⟩ : Σ _ : Fin R, Site N)≠⟨e.1,t e.2⟩ :=
        fun h => hit (h.trans (edge e).symm)
      rw [ite_eq_right hit,ite_eq_right miss]
  unfold MarkedWorld.siteUnits
  refine (congrArg (fun n => n+hist*(seedRecords X c ⟨j,v⟩).length) (congrArg₂ Nat.add
    (physical (W).graph.src (source N) (fun _ => rfl))
    (physical (W).graph.dst (target N) (fun _ => rfl)))).trans ?_
  apply congrArg₂ Nat.add
  · unfold incidenceLoad
    apply congrArg₂ Nat.add
    · apply Finset.sum_congr rfl
      intro e _
      by_cases hit : v=source N e <;> by_cases hub : hubFlag N (source N e)=true <;>
        simp [hit,hub] <;> intro incompatible <;>
        first | exact (incompatible rfl).elim | exact (hit incompatible).elim
    · apply Finset.sum_congr rfl
      intro e _
      by_cases hit : v=target N e <;> by_cases hub : hubFlag N (target N e)=true <;>
        simp [hit,hub] <;> intro incompatible <;>
        first | exact (incompatible rfl).elim | exact (hit incompatible).elim
  · cases v <;> simp [seedRecords,hubFlag]

omit [Fintype G] in
theorem seed_mass (wire hist : ℕ) (v : G×Site N) (x : Block l) :
    blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      ((W).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist) v x=
      incidenceLoad N (wire*s) 256 v.2+(if hubFlag N v.2 then 0 else hist) := by
  obtain ⟨g,v⟩ := v
  unfold blockMass
  simp_rw [measure_seed X c wire hist]
  let a : (W).graph.Site := ⟨digits.symm (g,x),v⟩
  have pos : seedPos X c digits a=(g,v) := by simp [a,seedPos]
  have blk : seedBlock X c digits a=x := by simp [a,seedBlock]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · rw [ite_eq_left ⟨pos,blk⟩]
  · intro u _ different
    apply ite_eq_right
    rintro ⟨part,low⟩
    exact different (seed_coordinates X c digits (Prod.ext (part.trans pos.symm) (low.trans blk.symm)))

omit [Fintype G] in
theorem seed_small (wire hist : ℕ) (room : 3*(wire*s)+hist≤256*(wire*s)) (v : G×Site N) (x : Block l) :
    blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      ((W).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist) v x≤256*(wire*s) := by
  rw [seed_mass]
  exact old_cap N (physical_output X).1 _ _ room v.2

omit [Fintype G] in
theorem seed_hub_full (wire hist : ℕ) (g : G) (pin : Fin (Fintype.card (Port p X.width))) (x : Block l) :
    blockMass (W).graph (seedPos X c digits) (seedBlock X c digits)
      ((W).siteUnits (seedHub X c) (seedRecords X c) wire 256 hist) (g,.inr pin) x=256*(wire*s) := by
  rw [seed_mass]
  simp [hub_load,hubFlag,Nat.mul_comm]

theorem seed_record_total :
    (∑v : (W).graph.Site,(seedRecords X c v).length)=R*Fintype.card (N).Site := by
  change (∑u : Σ_ : Fin R,Site N,(seedRecords X c u).length)=_
  rw [Fintype.sum_sigma]
  simp [Fintype.sum_sum_type,seedRecords]

end
end Hierarchy.DescentInitialHost

end OAI
