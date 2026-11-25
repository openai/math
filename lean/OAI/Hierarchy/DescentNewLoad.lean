import OAI.Hierarchy.DescentScannedHost
import OAI.Hierarchy.DescentPostRecordedCap
import OAI.Hierarchy.DescentSubroundHubCapacity

namespace OAI
/-! # Both load bounds on actual post-subround native positions -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentHostDegree DescentColonies
open scoped BigOperators Classical
noncomputable section

private theorem sum_record_fibers {Source Target : Type} [Fintype Source] [Fintype Target]
    (loc : Source → Target) (weight : Source → ℕ)
    (enum : ∀ dest, Fintype {src : Source // loc src = dest}) :
    (∑ dest, ∑ entry ∈ @Finset.univ _ (enum dest), weight entry.val) = ∑ src, weight src := by
  classical
  have native := Fintype.sum_fiberwise loc weight
  refine Eq.trans ?_ native
  apply Finset.sum_congr rfl
  intro dest _
  exact congrArg (fun t : Fintype {src : Source // loc src = dest} =>
    ∑ entry ∈ @Finset.univ _ t, weight entry.val) (Subsingleton.elim _ _)

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
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i ≤ scale * B) (sheet : Block k→Bool)
variable (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
abbrev scannedHome :=
  recordedHome W pos ix near (flag ∘ pos) rec wire β hist a₀ Δ (scale * B) small

abbrev scannedPairs :=
  recordedPairs W pos ix near (flag ∘ pos) rec wire β hist a₀ Δ (scale * B) B small sheet

abbrev scannedPairEdge :=
  recordedPick W pos ix near (flag ∘ pos) rec wire β hist a₀ Δ (scale * B) B small sheet

local notation "home" => scannedHome W pos ix near flag rec wire β hist a₀ Δ B scale small
local notation "col" => occupiedAddress N U near D a load small pos ix
local notation "paint" => (sheet∘ix)
local notation "pick" => scannedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
local notation "pack" => coloredPack N W.core home paint B
local notation "I" => scannedPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
variable (z : scannedPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (fit : ∀ i (s : Fin 2),
  W.graph.width (scannedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet (i,s)) = z i * G.b)
variable (p : scannedPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
local notation "lay" => bestLayout (branchWidth G z p)
local notation "colors" => (fun e (_ : e∈W.core)=>congrArg sheet (same e))
local notation "key" => nativeKey N W.core home paint B col colors lay
/-- The coalesced marked world on the selected physical graph with its scanned host addresses. -/
abbrev scannedCoalesced := MarkedWorld.coalesced sel key flag k (gainExponent a₀ Δ)

local notation "post" => scannedCoalesced W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p

variable (ag : packExponent a₀ Δ ≤ gainExponent a₀ Δ) (gk : gainExponent a₀ Δ ≤ k)
variable (inc : MarkedWorld.HubIncidence W (flag∘pos)) (picked : ∀ t : (scannedPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet) × Fin 2,
  scannedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet t ∈ W.core)
local notation "join" => scanned_pack_flags W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
local notation "mark" => W.selectedHub G pick z hz fit pack p (flag∘pos) inc picked join
local notation "born" => newRecords N pick lay pack rec z p
local notation "finalAtoms" => MarkedWorld.coalescedRecords sel key flag k g born
variable (oldEmpty : ∀u,flag (pos u)=true → rec u=[])
variable (filled : ∀ v, flag v = true → ∀ i,
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i = scale * B)

include inc picked oldEmpty in
theorem new_hub_empty {v : (post).graph.Site} (yes : flag v.val.1=true) : finalAtoms v=[] := by
  apply MarkedWorld.coalescedRecords_empty sel key flag k g born _ yes
  intro t atHub
  exact hub_empty N pick lay pack rec z p mark oldEmpty (fun _=>rfl)
    ((scanned_hub_flags W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p inc picked t).symm.trans atHub)

variable (q : ℕ) (counts : (scannedCoalesced
  W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p).graph.Edge → ℕ)
variable (cut : ∀ e : (scannedCoalesced W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p).graph.Edge, e ∈ (scannedCoalesced W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p).core →
  (scannedCoalesced W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p).graph.width e = counts e * q)
local notation "W₁" => MarkedWorld.pieces post q counts cut
local notation "actual" => MarkedWorld.siteUnits W₁ (MarkedWorld.coalescedHub sel key flag k g) finalAtoms wire β hist

include ag gk inc picked oldEmpty filled in
theorem post_hub_full (positive : 0<U) (v : (W₁).graph.Site) (yes : flag v.val.1=true) :
    actual v=2^g*U := by
  have unpaid : ∀i,flag (pos (W.graph.src (pick (i,1))))=false := fun i=>(inc.inside _ (picked (i,1))).1
  have first := native_old_hub W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z p unpaid filled positive
  exact MarkedWorld.selected_coalesced_pieces_hub W G pick z hz fit pack p pos ix flag inc picked join key q counts cut
    rec finalAtoms wire β hist U oldEmpty
    (fun _ marked => new_hub_empty W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same
      z hz fit p inc picked oldEmpty marked)
    (scanned_hub_flags W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p inc picked)
    (fun u h => congrArg (fun t : V × (ℕ × ℕ) => t.1) (first u h))
    (fun u h => congrArg (fun t : V × (ℕ × ℕ) => t.2) (first u h))
    ag gk filled v yes

include ag gk inc picked oldEmpty filled in
theorem post_paid (hb : 0<B) (hs : 0<scale) (hβ : 1≤β)
    (paid : ∀e∈W.core,scale≤wire*W.graph.width e)
    (birth : ∀i s,6*hist≤wire*W.graph.width (pick (i,s)))
    (degree : ∀v,(near v).card≤Δ)
    (adj : ∀e∈W.core,pos (W.graph.dst e)∈near (pos (W.graph.src e)) ∧ pos (W.graph.src e)∈near (pos (W.graph.dst e)))
    (v : (W₁).graph.Site) : actual v≤2^g*U := by
  cases yes : flag v.val.1 with
  | true =>
    exact (post_hub_full W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p ag gk inc picked
      oldEmpty filled q counts cut (Nat.mul_pos hs hb) v yes).le
  | false =>
    exact post_recorded_nonhub_cap W G pos ix near (flag∘pos) rec wire β hist a₀ Δ U B small sheet z hz p fit
      key flag q counts cut hβ hb scale hs rfl paid birth degree adj (fun e _=>same e) v yes

omit [Fintype V] in
theorem post_atom_count :
    (∑v : (post).graph.Site,(finalAtoms v).length)=(∑u,(rec u).length)+6*Fintype.card I := by
  let loc : (sel).graph.Site → (post).graph.Site := MarkedWorld.address sel key flag k g
  calc
    _ = ∑ v : (post).graph.Site, ∑ u : {u : (sel).graph.Site // loc u = v}, (born u.val).length :=
      Finset.sum_congr rfl (fun v _ => MarkedWorld.coalescedRecords_length sel key flag k g born v)
    _ = ∑ u : (sel).graph.Site, (born u).length :=
      sum_record_fibers loc (fun u => (born u).length) (fun b =>
        @Subtype.fintype (sel).graph.Site (fun src => loc src = b)
          (fun src => Classical.propDecidable (loc src = b)) (sel).graph.finiteSite)
    _ = _ := newRecords_total N pick lay pack rec z p

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
