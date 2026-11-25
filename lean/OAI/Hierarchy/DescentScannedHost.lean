import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentNativeHubKeys
import OAI.Hierarchy.DescentScaledOccupiedGain
import OAI.Hierarchy.DescentNextCoordinates
import OAI.Hierarchy.DescentCoalescedRecords

namespace OAI
/-! # The actual surviving positions, coordinates and cables of the common subround host -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentHostDegree DescentColonies
open scoped BigOperators Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {d k : ℕ} {P : Type} {bits : P→ℕ}
variable {F : Type} [Field F] (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k) (near : V→Finset V) (flag : V→Bool)
variable {T : Type} (rec : W.graph.Site→List T) (wire β hist a₀ Δ B scale : ℕ)
local notation "a" => packExponent a₀ Δ
local notation "g" => gainExponent a₀ Δ
local notation "D" => gap Δ
local notation "U" => (scale*B)
local notation "full" => W.siteUnits (flag∘pos) rec wire β hist
local notation "load" => blockMass N pos ix full
variable (small : ∀ (v : V) (i : Block k),
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i ≤ scale * B)
variable (sheet : Block k → Bool)
variable (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
private abbrev hostHome :=
  occupiedHome W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist)
    near (gap Δ) (packExponent a₀ Δ) (scale * B) small

private abbrev hostPairs :=
  NativePair W.graph W.core (hostHome W pos ix near flag rec wire β hist a₀ Δ B scale small) (sheet ∘ ix) B

private abbrev selectedPairEdge :=
  colorPick W.graph W.core (hostHome W pos ix near flag rec wire β hist a₀ Δ B scale small) (sheet ∘ ix) B

variable (z : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (fit : ∀ i (s : Fin 2),
  W.graph.width (selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet (i,s)) = z i * G.b)
variable (p : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → Profile G.C)

local notation "home" => hostHome W pos ix near flag rec wire β hist a₀ Δ B scale small
local notation "col" => occupiedAddress N U near D a load small pos ix
local notation "paint" => (sheet ∘ ix)
local notation "pick" => selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
local notation "pack" => coloredPack N W.core home paint B
local notation "sel" => W.selected G pick z hz fit pack p
local notation "lay" => bestLayout (branchWidth G z p)
local notation "colors" => (fun e (_ : e∈W.core)=>congrArg sheet (same e))
local notation "key" => nativeKey N W.core home paint B col colors lay
local notation "post" => MarkedWorld.coalesced sel key flag k g

theorem selected_address (hb : 0<B) (hs : 0<scale) (hβ : 1≤β)
    (paid : ∀e∈W.core,scale≤wire*W.graph.width e) (v : (sel).graph.Site) :
    key v∈keys k (2^a+2) := by
  have cap := scaled_pair_cap N pos ix full near a₀ Δ U B small W.core sheet scale hs rfl
    (W.siteUnits_outgoing (flag∘pos) rec wire β hist home scale paid hβ)
  exact pack_mem N W.core home paint B col near D a load small pos ix _ hb cap
    (colonyOf_surjective N U near D a load small pos ix) (occupiedAddress_colonyOf N U near D a load small pos ix) _

omit [Fintype V] in
theorem selected_span (hb : 0<B) (hs : 0<scale) (hβ : 1≤β)
    (paid : ∀e∈W.core,scale≤wire*W.graph.width e)
    (adj : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)) ∧ pos (W.graph.src e)∈near (pos (W.graph.dst e))) (e : (sel).graph.Edge) :
    key ((sel).graph.dst e)∈directory near D (2^a+2) 8 (key ((sel).graph.src e)) ∧
      key ((sel).graph.src e)∈directory near D (2^a+2) 8 (key ((sel).graph.dst e)) := by
  have cap := scaled_pair_cap N pos ix full near a₀ Δ U B small W.core sheet scale hs rfl
    (W.siteUnits_outgoing (flag∘pos) rec wire β hist home scale paid hβ)
  exact native_cables_both N W.core home paint B col near D a load small pos ix _ hb cap
    (occupiedAddress_colonyOf N U near D a load small pos ix) same adj sheet (fun _=>rfl) lay (branchWidth G z p)
    (fun _ => (0 : EuclideanSpace ℝ (Fin d))) (fun _ => by simp) e

variable (ag : packExponent a₀ Δ ≤ gainExponent a₀ Δ) (gk : gainExponent a₀ Δ ≤ k)
variable (unpaid : ∀ i : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet,
  flag (pos (W.graph.src (selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet (i,1)))) = false)
variable (filled : ∀ v, flag v = true → ∀ i,
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i = scale * B)

include unpaid filled in
omit [Fintype V] in
theorem native_old_hub (positive : 0<U) (u : W.graph.Site) (yes : flag (pos u)=true) :
    let addr:=key (newSite N pick lay pack (.inl u))
    (addr.1,addr.2.1)=(pos u,(k-a,group (k-a) (ix u))) :=
  native_hub_interval N W.core home paint B col colors lay flag
    (fun i => (congrArg (fun t : V × (ℕ × ℕ) => flag t.1)
      (occupiedAddress_colonyOf N U near D a load small pos ix (W.graph.src (pick (i,1))))).trans (unpaid i))
    near D load small positive
    filled pos ix (occupiedAddress_colonyOf N U near D a load small pos ix) u yes

omit [Field F] in
theorem scanned_pack_flags (u v : W.graph.Site) (merge : pack u=pack v) : flag (pos u)=flag (pos v) :=
  MarkedWorld.colored_pack_hub W pos ix full near D a U B small paint flag u v merge

variable (inc : MarkedWorld.HubIncidence W (flag ∘ pos))
variable (picked : ∀ t : (hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet) × Fin 2,
  selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet t ∈ W.core)
local notation "join" => scanned_pack_flags W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
local notation "mark" => W.selectedHub G pick z hz fit pack p (flag∘pos) inc picked join

theorem scanned_hub_flags (v : (sel).graph.Site) : flag (key v).1=mark v :=
  MarkedWorld.native_key_hub N W.core home paint B col colors lay flag mark
    (fun u => (congrArg (fun t : V × (ℕ × ℕ) => flag t.1)
      (occupiedAddress_colonyOf N U near D a load small pos ix u)).symm) v

include ag gk unpaid filled in
omit [Fintype V] in
theorem old_address (u : W.graph.Site) (yes : flag (pos u)=true) (positive : 0<U) :
    (MarkedWorld.address sel key flag k g (newSite N pick lay pack (.inl u))).val=
      (pos u,(k-g,group (k-g) (ix u)),0) := by
  have exactPrefix := native_old_hub W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same
    z p unpaid filled positive u yes
  let x := key (newSite N pick lay pack (.inl u))
  have eq : x=(pos u,(k-a,group (k-a) (ix u)),x.2.2) :=
    congrArg (fun t : V × (ℕ × ℕ) => (t.1,t.2,x.2.2)) exactPrefix
  change mergeHub flag k g x=_
  rw [eq,merge_hub_read flag ag gk (pos u) yes (ix u)]

include unpaid filled inc picked in
theorem selected_hub_interval (positive : 0<U) (u : (sel).graph.Site) (hh : flag (key u).1=true) :
    ∃b : Block k,(key u).2.1=(k-a,group (k-a) b) := by
  obtain ⟨x,rfl⟩ := old_surjective N pick lay pack u
  have read := scanned_hub_flags W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same
    z hz fit p inc picked (newSite N pick lay pack (.inl x))
  have yes : flag (pos x)=true := read.symm.trans hh
  exact ⟨ix x,congrArg Prod.snd (native_old_hub W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet
    same z p unpaid filled positive x yes)⟩

include ag gk unpaid filled inc picked in
theorem post_address (hb : 0<B) (hs : 0<scale) (hβ : 1≤β)
    (paid : ∀e∈W.core,scale≤wire*W.graph.width e)
    (v : (post).graph.Site) : v.val∈keys k (2^a+2) := by
  obtain ⟨u,_,atPos⟩ := Finset.mem_image.mp v.property
  have original := selected_address W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p hb hs hβ paid u
  change mergeHub flag k g (key u)=v.val at atPos
  rw [←atPos]
  cases hh : flag (key u).1 with
  | false => simpa [mergeHub,hh] using original
  | true =>
    obtain ⟨t,tRead⟩ := selected_hub_interval W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same
      z hz fit p unpaid filled inc picked (Nat.mul_pos hs hb) u hh
    have exactKey : key u=((key u).1,(k-a,group (k-a) t),(key u).2.2) :=
      Prod.ext rfl (Prod.ext tRead rfl)
    rw [exactKey,merge_hub_read flag ag gk _ hh t]
    exact key_mem _ t (Nat.sub_le k g) (Nat.succ_pos (2^a+1))

include ag gk unpaid filled inc picked in
theorem post_span (hb : 0<B) (hs : 0<scale) (hβ : 1≤β)
    (paid : ∀e∈W.core,scale≤wire*W.graph.width e)
    (adj : ∀e,pos (W.graph.dst e)∈near (pos (W.graph.src e)) ∧ pos (W.graph.src e)∈near (pos (W.graph.dst e))) (e : (post).graph.Edge) :
    ((post).graph.dst e).val∈directory near (D+g) (2^a+2) 10 ((post).graph.src e).val ∧
      ((post).graph.src e).val∈directory near (D+g) (2^a+2) 10 ((post).graph.dst e).val := by
  have locations := selected_address W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p hb hs hβ paid
  have room (u : (sel).graph.Site) : (key u).2.2<2^a+2 :=
    Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp (locations u)).2).2
  have walk := selected_span W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p hb hs hβ paid adj e.val
  have saturated := selected_hub_interval W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same
    z hz fit p unpaid filled inc picked (Nat.mul_pos hs hb)
  exact ⟨merged_cable_hops flag near ag gk walk.1 (room _) (room _) (saturated _) (saturated _),
    merged_cable_hops flag near ag gk walk.2 (room _) (room _) (saturated _) (saturated _)⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
