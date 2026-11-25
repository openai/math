import OAI.Hierarchy.DescentSelectedHubs
import OAI.Hierarchy.DescentIntegralSiteLoad

namespace OAI
/-! # Endpoint multiplicity in an actual fiber of the hub quotient -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P : Type*} {bits : P→ℕ}

abbrev Tether (W : MarkedWorld F d P bits) := {e : W.graph.Edge // e∉W.core}

/-- A bijection of the surviving physical tethers, with their unchanged widths and endpoints. -/
structure TetherImage (W Z : MarkedWorld F d P bits) (loc : W.graph.Site→Z.graph.Site) where
  edges : Tether W ≃ Tether Z
  width : ∀e,Z.graph.width (edges e).val=W.graph.width e.val
  src : ∀e,Z.graph.src (edges e).val=loc (W.graph.src e.val)
  dst : ∀e,Z.graph.dst (edges e).val=loc (W.graph.dst e.val)

def TetherImage.comp {U W Z : MarkedWorld F d P bits} {loc : U.graph.Site→W.graph.Site}
    {dest : W.graph.Site→Z.graph.Site} (h : TetherImage U W loc) (t : TetherImage W Z dest) :
    TetherImage U Z (dest ∘ loc) where
  edges := h.edges.trans t.edges
  width e := (t.width _).trans (h.width e)
  src e := (t.src _).trans (congrArg dest (h.src e))
  dst e := (t.dst _).trans (congrArg dest (h.dst e))

private theorem endpoint_sum {U E : Type*} [Fintype U] [Fintype E]
    (keep : U→Prop) (atSite : E→U) (pay : E→ℕ) :
    (∑u, if keep u then ∑e, if u=atSite e then pay e else 0 else 0) =
    ∑e, if keep (atSite e) then pay e else 0 := by
  classical
  have inside (u : U) : (if keep u then ∑e, if u=atSite e then pay e else 0 else 0)=
      ∑e, if u=atSite e then (if keep (atSite e) then pay e else 0) else 0 := by
    by_cases h : keep u
    · rw [ite_eq_left h]
      apply Finset.sum_congr rfl;intro e _
      by_cases eqn : u=atSite e <;> simp_all
    · rw [ite_eq_right h];symm
      apply Finset.sum_eq_zero;intro e _
      by_cases eqn : u=atSite e <;> simp_all
  simp_rw [inside]
  rw [Finset.sum_comm]
  simp

omit [Field F] in
private theorem tether_end (W : MarkedWorld F d P bits) (hub : W.graph.Site→Bool)
    (keep : W.graph.Site→Prop) (atSite : W.graph.Edge→W.graph.Site) (wire β : ℕ)
    (hc : ∀e∈W.core,hub (atSite e)=false) (hk : ∀u,keep u→hub u=true) :
    (∑e,if keep (atSite e) then wire*W.graph.width e*(if hub (atSite e) then β else 1) else 0)=
    ∑e : Tether W, if keep (atSite e.val) then wire*W.graph.width e.val*β else 0 := by
  classical
  let f := fun e : W.graph.Edge=>if keep (atSite e) then wire*W.graph.width e*β else 0
  change _=∑e : Tether W,f e.val
  rw [← Finset.sum_subtype (Finset.univ.filter (fun e=>e∉W.core)) (by simp) f,Finset.sum_filter]
  apply Finset.sum_congr rfl;intro e _
  by_cases mem : e∈W.core
  · have missing : ¬keep (atSite e) := fun hy=>by have := (hc e mem).symm.trans (hk _ hy);contradiction
    simp [mem,missing,f]
  · by_cases yes : keep (atSite e)
    · simp [mem,yes,hk _ yes,f]
    · simp [mem,yes,f]

private def tetherEnds (W : MarkedWorld F d P bits) (keep : W.graph.Site→Prop) (wire β : ℕ) :=
  (∑e : Tether W,if keep (W.graph.src e.val) then wire*W.graph.width e.val*β else 0)+
  (∑e : Tether W,if keep (W.graph.dst e.val) then wire*W.graph.width e.val*β else 0)

omit [Field F] in
private theorem siteUnits_hub_sum {Aty : Type*} (W : MarkedWorld F d P bits)
    (hub : W.graph.Site→Bool) (inc : HubIncidence W hub) (rec : W.graph.Site→List Aty)
    (wire β hist : ℕ) (keep : W.graph.Site→Prop)
    (hk : ∀u,keep u→hub u=true) (empty : ∀u,keep u→ rec u=[]) :
    (∑u,if keep u then W.siteUnits hub rec wire β hist u else 0) = tetherEnds W keep wire β := by
  classical
  let side (endpoint : W.graph.Edge→W.graph.Site) (u : W.graph.Site) :=
    ∑e, if u=endpoint e then wire*W.graph.width e*(if hub (endpoint e) then β else 1) else 0
  have split (u) : (if keep u then W.siteUnits hub rec wire β hist u else 0)=
      (if keep u then side W.graph.src u else 0)+(if keep u then side W.graph.dst u else 0) := by
    by_cases h : keep u
    · simp [h, siteUnits, side, empty u h]
    · simp [h]
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  unfold side tetherEnds
  rw [endpoint_sum,endpoint_sum,tether_end W hub keep W.graph.src wire β (fun e h=>(inc.inside e h).1) hk,
    tether_end W hub keep W.graph.dst wire β (fun e h=>(inc.inside e h).2) hk]

omit [Field F] in
/-- At an actual hub with no stored atoms, the two endpoint columns are precisely the
sum of the original hub columns that land there. A loop would contribute both endpoints. -/
theorem TetherImage.siteUnits_fiber {Aty Bty : Type*} {W Z : MarkedWorld F d P bits}
    {loc : W.graph.Site→Z.graph.Site} (t : TetherImage W Z loc)
    (hW : W.graph.Site→Bool) (hZ : Z.graph.Site→Bool) (iW : HubIncidence W hW) (iZ : HubIncidence Z hZ)
    (old : W.graph.Site→List Aty) (newRec : Z.graph.Site→List Bty) (wire β hist : ℕ) (v : Z.graph.Site)
    (yes : hZ v=true) (same : ∀u,hZ (loc u)=hW u)
    (empty : ∀u,hW u=true→ old u=[]) (empty' : newRec v=[]) :
    Z.siteUnits hZ newRec wire β hist v=∑u,if loc u=v then W.siteUnits hW old wire β hist u else 0 := by
  classical
  have a := siteUnits_hub_sum Z hZ iZ newRec wire β hist (·=v)
    (by rintro u rfl;exact yes) (by rintro u rfl;exact empty')
  have oldHub (u) (hu : loc u=v) : hW u=true := by rw [←same u,hu];exact yes
  have b := siteUnits_hub_sum W hW iW old wire β hist (fun u=>loc u=v)
    oldHub (fun u hu=>empty u (oldHub u hu))
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at a
  rw [a,b]
  unfold tetherEnds
  congr 1
  · rw [← Equiv.sum_comp t.edges];simp only [t.src,t.width]
  · rw [← Equiv.sum_comp t.edges];simp only [t.dst,t.width]

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
