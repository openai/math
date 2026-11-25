import OAI.Hierarchy.DescentGroupStage
import OAI.Hierarchy.DescentOrdinarySuccessor

namespace OAI
/-! # Preservation of grouped ordinary and saturated placement through a complete selected update -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentHostDegree DescentHostDirectory
open GadgetNetwork MarkedWorld
open scoped BigOperators Classical
noncomputable section

variable {J J₁ V : Type} [Fintype J] [Fintype J₁] [Fintype V] [DecidableEq J] [DecidableEq J₁] [DecidableEq V]
variable {d k n : ℕ} {P : Type} {bits : P→ℕ} {F : Type} [Field F]
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable (pos : W.graph.Site→J×V) (ix : W.graph.Site→Block k) (near : V→Finset V) (flag : V→Bool)
variable {T : Type} (rec : W.graph.Site→List T) (wire hist Δ B scale : ℕ)
local notation "flags" => (fun v : J×V => flag (Prod.snd v))
local notation "old" => flags ∘ pos
local notation "β" => (256:ℕ)
local notation "a" => packExponent 20 Δ
local notation "g" => gainExponent 20 Δ
local notation "D" => gap Δ
local notation "slots" => (2^a+2)
local notation "U" => (scale*B)
local notation "nn" => groupedNear near
local notation "full" => W.siteUnits old rec wire β hist
variable (small : ∀ (v : J × V) (i : Block k),
  blockMass W.graph pos ix (W.siteUnits (fun u => flag (pos u).2) rec wire 256 hist) v i ≤ scale * B) (sheet : Block k→Bool)
variable (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
local notation "home" => scannedHome W pos ix nn flags rec wire β hist 20 Δ B scale small
local notation "col" => occupiedAddress N U nn D a (blockMass N pos ix full) small pos ix
local notation "paint" => (sheet∘ix)
local notation "pick" => scannedPairEdge W pos ix nn flags rec wire β hist 20 Δ B scale small sheet
local notation "pack" => coloredPack N W.core home paint B
local notation "I" => scannedPairs W pos ix nn flags rec wire β hist 20 Δ B scale small sheet
variable (z : scannedPairs W pos ix (groupedNear near)
  (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (fit : ∀ i (s : Fin 2),
  W.graph.width (scannedPairEdge W pos ix (groupedNear near) (fun v : J × V => flag v.2)
    rec wire 256 hist 20 Δ B scale small sheet (i,s)) = z i * G.b)
variable (p : scannedPairs W pos ix (groupedNear near)
  (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet → Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
local notation "lay" => bestLayout (branchWidth G z p)
local notation "colors" => fun e (_ : e∈W.core)=>congrArg sheet (same e)
local notation "key" => nativeKey N W.core home paint B col colors lay
local notation "coarse" => scannedCoalesced W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
local notation "born" => newRecords N pick lay pack rec z p
local notation "records" => coalescedRecords sel key flags k g born
local notation "billed" => (MarkedWorld.coalescedHub sel key flags k g)
variable (ag : packExponent 20 Δ ≤ gainExponent 20 Δ) (gk : gainExponent 20 Δ ≤ k)
variable (inc : HubIncidence W (fun u => flag (pos u).2))
variable (picked : ∀ t : (scannedPairs W pos ix (groupedNear near)
    (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet) × Fin 2,
  scannedPairEdge W pos ix (groupedNear near) (fun v : J × V => flag v.2)
    rec wire 256 hist 20 Δ B scale small sheet t ∈ W.core)
variable (oldEmpty : ∀ u, flag (pos u).2 = true → rec u = [])
variable (filled : ∀ v : J × V, flag v.2 = true → ∀ i,
  blockMass W.graph pos ix (W.siteUnits (fun u => flag (pos u).2) rec wire 256 hist) v i = scale * B)
variable (hb : 0<B) (hs : 0<scale) (paid : ∀e∈W.core,scale≤wire*W.graph.width e)
variable (birth : ∀ i (s : Fin 2),
  6 * hist ≤ wire * W.graph.width (scannedPairEdge W pos ix (groupedNear near) (fun v : J × V => flag v.2)
    rec wire 256 hist 20 Δ B scale small sheet (i,s)))
variable (degree : ∀v,(near v).card≤Δ)
variable (adj : ∀ e, pos (W.graph.dst e) ∈ groupedNear near (pos (W.graph.src e)) ∧
  pos (W.graph.src e) ∈ groupedNear near (pos (W.graph.dst e)))
variable (digits : J≃J₁×Block n)
variable (q : ℕ) (counts : (scannedCoalesced W G pos ix (groupedNear near)
    (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet same z hz fit p).graph.Edge → ℕ)
variable (cut : ∀ e : (scannedCoalesced W G pos ix (groupedNear near)
    (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet same z hz fit p).graph.Edge, e ∈ (scannedCoalesced W G pos ix (groupedNear near)
    (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet same z hz fit p).core →
  (scannedCoalesced W G pos ix (groupedNear near)
    (fun v : J × V => flag v.2) rec wire 256 hist 20 Δ B scale small sheet same z hz fit p).graph.width e = counts e * q)
local notation "W₁" => MarkedWorld.pieces coarse q counts cut
local notation "address" => (Function.Embedding.subtype (·∈reclaimed sel key flags k g))
local notation "keep" => (fun i => And.left (MarkedWorld.HubIncidence.inside inc _ (picked (i,1))))
local notation "join" => scanned_pack_flags W pos ix nn flags rec wire β hist 20 Δ B scale small sheet
local notation "mark" => W.selectedHub G pick z hz fit pack p old inc picked join
local notation "rootDegree" => (((Δ+1)*((D+g)+1+2*2^(D+g))*slots)^10)

local notation "entries" => ordinary_directory W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p
  ag gk inc picked filled hb hs paid
local notation "position" => nextPos address digits entries
local notation "block" => nextBlock address digits
local notation "near₁" => groupedNear (restrictedNear near (D+g) k slots)

set_option maxHeartbeats 800000 in
include ag gk inc picked oldEmpty filled hb hs paid birth degree adj digits in
def ordinary_group (unit cap₁ : ℕ) (hn : 0<n) (hu : 0<unit) (cap : 0<cap₁) (hw : 0<wire)
    (hq : q=unit*G.b) (scaleEq : 2^g*U=wire*(unit*G.b)*cap₁)
    (price ε : ℝ) (pp : 0<price)
    (atomBill : price*hist*((∑u,(rec u).length)+6*Fintype.card I:ℕ)≤ε)
    (hostBill : ((Fintype.card J₁* (Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 rootDegree*(price*((2^g*U:ℕ):ℝ)))≤ε) :
    GroupStage W₁ G price ε J₁ (Host V k slots) n := by
  let T₁ := ordinary_successor W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    oldEmpty filled hb hs paid birth degree adj digits q counts cut unit cap₁ hn hu cap hw hq scaleEq price ε pp atomBill hostBill
  have flagsEq : (fun t : (W₁).graph.Site=>publishedHub flag k g (position t).2.val)=billed := by
    funext u
    exact ordinary_flag W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p u
  have allEdges := ordinary_close W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    filled hb hs paid adj digits q counts cut
  refine {
    Atoms := Record T G.C
    wire := wire
    hist := hist
    z := unit
    cap := cap₁
    degree := rootDegree
    pos := position
    «block» := block
    near := restrictedNear near (D+g) k slots
    hub := fun u => publishedHub flag k g u.val
    «records» := records
    fieldBits := hn
    degreeMin := T₁.degreeMin
    degreeBound := restricted_degree near (D+g) k slots Δ degree
    symmetric := restricted_symmetric near (D+g) k slots
    pricePos := pp
    wirePos := hw
    unitPos := hu
    capPos := cap
    small := ?_
    saturated := ?_
    noHubAtoms := ordinary_empty W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p
      ag gk inc picked oldEmpty filled hb hs paid digits
    peers := fun e => ⟨(allEdges e).1,(allEdges e).2.1⟩
    same := fun e => (allEdges e).2.2
    incidence := ?_
    widths := T₁.widths
    retained := T₁.retained
    roots := ?_ }
  · change ∀v i,blockMass (W₁).graph position block
      ((W₁).siteUnits (fun t=>publishedHub flag k g (position t).2.val) records wire 256 hist) v i≤_
    rw [flagsEq]
    exact T₁.small
  · intro v hv i
    change blockMass (W₁).graph position block
      ((W₁).siteUnits (fun t=>publishedHub flag k g (position t).2.val) records wire 256 hist) v i=_
    have transportMass := congrArg (fun mask : (W₁).graph.Site → Bool =>
      blockMass (W₁).graph position block ((W₁).siteUnits mask records wire 256 hist) v i) flagsEq
    exact transportMass.trans ((ordinary_filled W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
      oldEmpty filled hb hs paid digits q counts cut v i hv).trans scaleEq)
  · exact (congrArg (fun mask : (W₁).graph.Site → Bool => HubIncidence W₁ mask) flagsEq).mpr
      (ordinary_incidence W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p
        inc picked q counts cut)
  · have previous := T₁.roots
    change (Fintype.card (J₁ × Host V k slots) : ℝ) *
      ((2:ℝ)^packExponent 20 rootDegree * (price * ((wire * (unit * G.b) * cap₁ : ℕ) : ℝ))) ≤ ε at previous
    simpa only [Fintype.card_prod] using previous

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
