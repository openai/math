import OAI.Hierarchy.DescentHubTetherImages
import OAI.Hierarchy.DescentMergedHub

namespace OAI
/-! # Exact hub capacity after merging a block of external stacks -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentColonies DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P V : Type} {bits : P→ℕ} [DecidableEq V] {k g : ℕ}

omit [Field F] in
private theorem block_units (W : MarkedWorld F d P bits) (pos : W.graph.Site→V)
    (ix : W.graph.Site→Block k) (full : W.graph.Site→ℕ) (v : V) (x : Block k) (hg : g≤k)
    (B : ℕ) (filled : ∀j,StarKeys.blockMass W.graph pos ix full v j=B) :
    (∑u,if pos u=v ∧ group (k-g) (ix u)=group (k-g) x then full u else 0)=2^g*B := by
  classical
  let s := interval (k-g) x
  have count : s.card=2^g := by
    rw [interval_card_eq (Nat.sub_le k g),width,Nat.sub_sub_self hg]
  calc
    _ = ∑j∈s,StarKeys.blockMass W.graph pos ix full v j := by
      unfold StarKeys.blockMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro u _
      by_cases eqv : pos u=v
      · have mem : ix u∈s ↔ group (k-g) (ix u)=group (k-g) x := by simp [s,interval]
        simp [eqv,←mem,eq_comm]
      · simp [eqv]
    _ = s.card*B := by simp [filled]
    _ = _ := by rw [count]

omit [Field F] in
/-- Each realized coarse hub contains exactly `2^g` old full block rows. The tether
bijection accounts for both endpoint columns across substitution, coalescence and unbundling. -/
theorem TetherImage.saturated_hub {Aty Bty : Type*} {W Z : MarkedWorld F d P bits}
    {loc : W.graph.Site→Z.graph.Site} (t : TetherImage W Z loc)
    (pos : W.graph.Site→V) (ix : W.graph.Site→Block k) (hub : V→Bool)
    (key : Z.graph.Site→Key V) (inj : Function.Injective key)
    (oldInc : HubIncidence W (hub ∘ pos)) (newInc : HubIncidence Z (fun v=>hub (key v).1))
    (old : W.graph.Site→List Aty) (post : Z.graph.Site→List Bty) (wire β hist B : ℕ)
    (oldEmpty : ∀u,hub (pos u)=true→ old u=[]) (newEmpty : ∀u,hub (key u).1=true→post u=[])
    (same : ∀u,hub (key (loc u)).1=hub (pos u)) (hg : g≤k)
    (address : ∀u,hub (pos u)=true→key (loc u)=(pos u,(k-g,group (k-g) (ix u)),0))
    (full : ∀v,hub v=true→∀j,StarKeys.blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) old wire β hist) v j=B)
    (v : Z.graph.Site) (yes : hub (key v).1=true) (realized : ∃u,loc u=v) :
    Z.siteUnits (fun u=>hub (key u).1) post wire β hist v = 2^g*B := by
  classical
  obtain ⟨x,rfl⟩ := realized
  have hx := (same x).symm.trans yes
  have cond (u : W.graph.Site) : loc u=loc x ↔ pos u=pos x ∧ group (k-g) (ix u)=group (k-g) (ix x) := by
    constructor
    · intro h
      have hu := (same u).symm.trans (by simpa only [h] using yes)
      have r := congrArg key h
      rw [address u hu,address x hx] at r
      exact ⟨congrArg Prod.fst r,congrArg (fun e : Key V=>e.2.1.2) r⟩
    · rintro ⟨hp,hi⟩
      apply inj
      have hu : hub (pos u)=true := hp ▸ hx
      rw [address u hu,address x hx,hp,hi]
  rw [t.siteUnits_fiber (hub ∘ pos) (fun u=>hub (key u).1) oldInc newInc old post wire β hist
    (loc x) yes same oldEmpty (newEmpty _ yes)]
  simp_rw [cond]
  exact block_units W pos ix _ (pos x) (ix x) hg B (full _ hx)

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
