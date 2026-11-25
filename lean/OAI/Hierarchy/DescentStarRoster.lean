import OAI.Hierarchy.DescentPackMass
import OAI.Hierarchy.DescentPaidHostGain

namespace OAI
/-! # The actual packs represented at one merged star -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDegree GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} {P : Type*} {bits : P→ℕ}
    (N : Network n P bits) (core : Finset N.Edge) (home : N.Site→C)
    (color : N.Site→Bool) (B : ℕ) (allow : C→Finset C)

abbrev NativePack := C⊕NativeSlot N core home color B

/-- For a thick key include the thick pack and the physically allocated thin slots
at allowed source colonies. A singleton thin key names just its own old pack. -/
def roster : NativePack N core home color B → Finset (NativePack N core home color B)
  | .inl c => ({c} : Finset C).disjSum ((allow c).sigma fun _=>Finset.univ)
  | .inr s => {.inr s}

theorem roster_card (A K : ℕ) (pos : 0<B) (small : ∀c,(allow c).card≤K)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤A*B)
    (p : NativePack N core home color B) : (roster N core home color B allow p).card≤1+K*(A+1) := by
  rcases p with c|s
  · simp only [roster,Finset.card_disjSum,Finset.card_singleton,Finset.card_sigma,Finset.card_univ]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑_∈allow c,(A+1) := Finset.sum_le_sum fun d _=>slots_bound
        (fun _=>nativeTraffic N core home) B (thinList home color) (thickList home color) d pos (cap d)
      _ = (allow c).card*(A+1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (small c)
  · simp [roster]

variable (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool)

include same in
/-- In the second layout the selected target is reached by the thick atom's
original core cable. In the first layout both packs share their source colony. -/
theorem center_source (self : ∀c,c∈allow c) (old : ∀e∈core,home (N.src e)∈allow (home (N.dst e)))
    (i : NativePair N core home color B) :
    i.1∈allow (chosenCenter N core home color B l i) := by
  cases l with
  | false => exact self i.1
  | true =>
    let e := colorPick N core home color B (i,0)
    have isCore : e∈core := pairedCore_mem N core (fun e=>home (N.dst e)) home B
      (thinList home color) (thickList home color)
      (colorSites_nodup home color false) (colorSites_nodup home color true)
      (colorSites_disjoint home color)
      (fun _ _ h => ((mem_colorSites ..).mp h).1)
      (fun _ _ h => ((mem_colorSites ..).mp h).1) (i,0)
    have hs : home (N.src e)=i.1 := (pack_home N B home color core _).symm.trans
      (congrArg packColony (colorPick_thick_src N core home color B i))
    have ht : home (N.dst e)=i.2.1 := (pack_home N B home color core _).symm.trans
      (congrArg packColony (colorPick_thick_dst N core home color B same i))
    change i.1∈allow i.2.1
    exact (congrArg₂ (fun a b : C => a ∈ allow b) hs ht).mp (old e isCore)

def starLabel := key N (colorPick N core home color B) l (coloredPack N core home color B)
  (chosenSlot N core home color B) (chosenCenter N core home color B l)
  (colorPick_thin_src N core home color B) (native_centerAt N core home color B same l)
  (native_coherent _ B _ _ (fun _ c=>c) l)

theorem roster_covers (self : ∀c,c∈allow c) (old : ∀e∈core,home (N.src e)∈allow (home (N.dst e)))
    (v : Merged N (colorPick N core home color B) l (coloredPack N core home color B))
    (u : N.Site) (atSite : newSite N (colorPick N core home color B) l (coloredPack N core home color B)
      (.inl u)=v) : coloredPack N core home color B u∈roster N core home color B allow
        (starLabel N core home color B same l v) := by
  subst v
  let slot := chosenSlot N core home color B
  let center := chosenCenter N core home color B l
  change coloredPack N core home color B u∈roster _ _ _ _ _ _ (resolve slot center (coloredPack N core home color B u))
  generalize coloredPack N core home color B u=p
  rcases p with c|s
  · simp [resolve,roster]
  · by_cases hit : ∃i,slot i=s
    · rw [resolve,dite_eq_left hit,roster,Finset.inr_mem_disjSum,Finset.mem_sigma]
      have homeEq : hit.choose.1=s.1 := congrArg Sigma.fst hit.choose_spec
      exact ⟨homeEq ▸ center_source N core home color B allow same l self old hit.choose,Finset.mem_univ _⟩
    · simp [resolve,hit,roster]

include same in
/-- The preceding generic paid-gain estimate applies to the computed roster
of this branch and this quotient site. -/
theorem native_paid_gain {F : Type*} [Field F] (G : PoweredGadget F)
    (self : ∀c,c∈allow c) (old : ∀e∈core,home (N.src e)∈allow (home (N.dst e)))
    (a₀ Δ : ℕ) (positive : 0<B) (small : ∀c,(allow c).card≤allowedSources Δ)
    (cap : ∀c,amount (live (nativeTraffic N core home)) (thinList home color c)≤2^packExponent a₀ Δ*B)
    (carried : N.Site→ℕ) (paid : ∀c : NativePack N core home color B,
      (∑u : N.Site,if coloredPack N core home color B u=c then siteLoad N u+carried u else 0)
        ≤2^packExponent a₀ Δ*B)
    (z : NativePair N core home color B→ℕ) (p : NativePair N core home color B→Profile G.C)
    (fit : ∀i s,N.width (colorPick N core home color B (i,s))=z i*G.b) {d : ℕ}
    (pos : Merged N (colorPick N core home color B) l (coloredPack N core home color B)→EuclideanSpace ℝ (Fin d))
    (hpos : ∀q,‖pos q‖≤1) (v) :
    let pick:=colorPick N core home color B
    let pack:=coloredPack N core home color B
    let w:=fun i e=>z i*(((p i).1 e).val+G.k)
    2*(siteLoad (merged N pick w l pack pos hpos) v+
      ∑u : {u : N.Site // newSite N pick l pack (.inl u)=v},carried u.val)≤2^gainExponent a₀ Δ*B := by
  let chosen := starLabel N core home color B same l v
  apply paid_host_gain N (colorPick N core home color B) l (coloredPack N core home color B)
    pos hpos v G z p fit carried (roster N core home color B allow chosen) a₀ Δ B
    (roster_covers N core home color B allow same l self old v)
    (roster_card N core home color B allow _ _ positive small cap chosen)
  intro c _
  refine le_trans ?_ (paid c)
  apply Finset.sum_le_sum
  intro u _
  exact le_of_eq (@ite_cond_congr ℕ _ _
    (Classical.propDecidable (coloredPack N core home color B u = c))
    (inferInstanceAs (Decidable (coloredPack N core home color B u = c))) _ _ rfl)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
