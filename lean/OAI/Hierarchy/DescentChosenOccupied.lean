import OAI.Hierarchy.DescentPackMass
import OAI.Hierarchy.DescentColonySelection

namespace OAI
/-! # Selecting the block addresses used by the physical pairing invoice -/

namespace Hierarchy.DescentSixParty.StarKeys

open Computability.BorderVNP.Crossing DescentColonies DescentGL
open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (position : N.Site→V) (block : N.Site→Block k) (full : N.Site→ℕ)

/-- Apply the same invertible block-address permutation to all old sites. -/
def reindexedBlock (L : Layout k) (u : N.Site) : Block k := rearrange L (block u)

omit [Fintype V] in
theorem blockMass_reindexed (L : Layout k) :
    blockMass N position (reindexedBlock N block L) full = rearrangedLoad (blockMass N position block full) L := by
  funext v i
  apply Finset.sum_congr rfl
  intro u _
  have test : reindexedBlock N block L u=i ↔ block u=(rearrange L).symm i := (rearrange L).eq_symm_apply.symm
  simp only [test]

theorem total_blockMass : (∑v,∑i,blockMass N position block full v i)=∑u,full u := by
  unfold blockMass
  calc
    _ = ∑v,∑u : N.Site,∑i : Block k, if position u=v ∧ block u=i then full u else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑u : N.Site,∑v,∑i : Block k, if position u=v ∧ block u=i then full u else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      have inner (v : V) : (∑i : Block k,if position u=v ∧ block u=i then full u else 0) =
          if position u=v then full u else 0 := by by_cases eqn : position u=v <;> simp [eqn]
      simp_rw [inner]
      simp

omit [Fintype V] in
theorem small_reindexed {B : ℕ} (small : ∀v i,blockMass N position block full v i≤B) (L : Layout k) :
    ∀v i,blockMass N position (reindexedBlock N block L) full v i≤B := by
  intro v i
  rw [blockMass_reindexed]
  exact small _ _

/-- Every occupied key in the actual invoice is a member of the full
leaf directory used to score the multiplier. -/
theorem occupied_card_le {B D a : ℕ} (near : V→Finset V) (load load' : V→Block k→ℕ)
    (eqn : load=load') (small : ∀v i,load v i≤B) (small' : ∀v i,load' v i≤B) :
    Fintype.card (occupied N B near D a load small position block)≤
      (leaves load' (fun v w=>w∈near v) D a B small').card := by
  subst load'
  rw [Fintype.card_coe]
  apply Finset.card_le_card
  intro key member
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp member
  exact Finset.mem_biUnion.mpr ⟨position u,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨block u,Finset.mem_univ _,rfl⟩⟩

theorem reindexed_preserves {L : Layout k} {u v : N.Site} (same : block u=block v) :
    reindexedBlock N block L u=reindexedBlock N block L v := congrArg (rearrange L) same

/-- The minimizing shared multiplier supplies the very block map and occupied
colony count needed by `selected_invoice`; the numerator is the total input
site load, including carried descriptions. -/
theorem chosen_occupied_colonies (hk : 0<k) (near : V→Finset V) (a B Δ : ℕ)
    (small : ∀v i,blockMass N position block full v i≤B) (degree : ∀v,(near v).card≤Δ)
    (branch : 2≤Δ) (scale : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    let load := blockMass N position block full
    let Q := fun μ : Nonzero k => colonyCount (fun _ : Unit => load) (fun v w=>w∈near v)
      a B Δ (fun _=>small) (multiplier hk μ)
    ∃ μ : Nonzero k, (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ) ∧
      let L := multiplier hk μ
      let chosen := reindexedBlock N block L
      (Fintype.card (occupied N B near D a (blockMass N position chosen full)
        (small_reindexed N position block full small L) position chosen):ℝ)≤
        Fintype.card V + 240*(∑u : N.Site,(full u:ℝ))/(2^a*B:ℕ) := by
  let load := blockMass N position block full
  let groupLoad := fun _ : Unit => load
  let adj := fun v w : V => w∈near v
  have deg (v : V) : (DescentColonies.next adj v).card≤Δ := by
    have eqn : DescentColonies.next adj v=near v := Finset.ext fun w=>by simp [DescentColonies.next,adj]
    simpa only [eqn] using degree v
  obtain ⟨_, μ,chosen,_,price⟩ := scanned_multiplier_colonies hk groupLoad adj a B Δ
    (fun _=>small) deg branch scale two
  refine ⟨μ,chosen,?_⟩
  let L := multiplier hk μ
  let place := reindexedBlock N block L
  let D := 32*Nat.clog 2 (2*Δ)
  have count := occupied_card_le (D:=D) (a:=a) N position place near (blockMass N position place full)
    (rearrangedLoad load L) (blockMass_reindexed N position block full L)
    (small_reindexed N position block full small L) (fun v i=>small v ((rearrange L).symm i))
  have total : (∑v,∑i,(load v i:ℝ))=∑u : N.Site,(full u:ℝ) := by exact_mod_cast total_blockMass N position block full
  apply (show (Fintype.card (occupied N B near D a (blockMass N position place full)
    (small_reindexed N position block full small L) position place):ℝ)≤
    ((leaves (rearrangedLoad load L) adj D a B (fun v i=>small v ((rearrange L).symm i))).card:ℝ)
    by exact_mod_cast count).trans
  simpa only [colonyCount,groupLoad,Fintype.sum_unique,Fintype.card_unit,Nat.cast_one,one_mul,total,D,L,adj] using price

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
