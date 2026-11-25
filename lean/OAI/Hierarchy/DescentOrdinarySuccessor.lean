import OAI.Hierarchy.DescentHubOccupancy
import OAI.Hierarchy.DescentSubroundNormalize
import OAI.Hierarchy.DescentNewLoad
import OAI.Hierarchy.DescentMeasuredHistory

namespace OAI
/-! # Re-entering the genuine shrinker after a native occupied-color update -/

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

include ag gk inc picked filled hb hs paid in
theorem ordinary_directory (v : (coarse).graph.Site) : (splitKey (address v)).2∈keys (V:=V) k slots :=
  split_mem _ (post_address W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
    ag gk keep filled inc picked hb hs (by decide) paid v)

local notation "entries" => ordinary_directory W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p
  ag gk inc picked filled hb hs paid
local notation "position" => nextPos address digits entries
local notation "block" => nextBlock address digits
local notation "near₁" => groupedNear (restrictedNear near (D+g) k slots)

set_option maxHeartbeats 800000 in
include adj in
omit [Fintype J₁] [DecidableEq J₁] in
theorem ordinary_close (e : (W₁).graph.Edge) :
    position ((W₁).graph.dst e)∈near₁ (position ((W₁).graph.src e)) ∧
      position ((W₁).graph.src e)∈near₁ (position ((W₁).graph.dst e)) ∧
      block ((W₁).graph.src e)=block ((W₁).graph.dst e) := by
  let oldEdge := DescentCableUnbundling.original (coarse).graph (coarse).core counts e
  have h := post_span W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
    ag gk keep filled inc picked hb hs (by decide) paid adj oldEdge
  have fwd := next_close address digits entries near («D»:=D+g)
    (u:=(coarse).graph.src oldEdge) (v:=(coarse).graph.dst oldEdge) h.1 h.2
  have back := next_close address digits entries near («D»:=D+g)
    (u:=(coarse).graph.dst oldEdge) (v:=(coarse).graph.src oldEdge) h.2 h.1
  exact ⟨fwd.1,back.1,back.2⟩

include inc picked in
theorem ordinary_incidence : HubIncidence W₁ billed := by
  apply pieces_hubs
  apply coalesced_hubs _ _ _ _ _ mark (selected_hubs W G pick z hz fit pack p old inc picked join)
  exact scanned_hub_flags W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p inc picked

include oldEmpty birth degree adj in
omit [Fintype J₁] in
theorem ordinary_mass (v : J₁×Host V k slots) (i : Block n) :
    blockMass (W₁).graph position block ((W₁).siteUnits billed records wire β hist) v i≤2^g*U := by
  apply next_mass
  exact post_paid W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p ag gk inc picked oldEmpty
    filled q counts cut hb hs (by decide) paid birth (fun v=>(grouped_degree near v).le.trans (degree v.2)) (fun e _=>adj e)

omit [Field F] [Fintype J] [Fintype V] in
private theorem published_flag_at_reclaimed (A : MarkedWorld F d P bits)
    (origin : A.graph.Site → Key (J × V)) (atHost : V → Bool) (width gain : ℕ)
    (row : reclaimed A origin (fun jv => atHost jv.2) width gain) :
    publishedHub atHost width gain (splitKey row.val).2 = atHost row.val.1.2 := by
  apply grouped_flag (v := row.val) atHost
  have hit := row.property
  unfold reclaimed at hit
  obtain ⟨u, _, placed⟩ := Finset.mem_image.mp hit
  change mergeHub (fun jv : J × V => atHost jv.2) width gain (origin u) = row.val at placed
  rw [← placed]
  by_cases exterior : atHost (origin u).1.2 = true <;> simp [mergeHub, exterior]

omit [Fintype J] [Fintype V] in
/-- The true hub flag of an occupied row agrees with the fixed Boolean
directory before any choice of its new block digit. -/
theorem ordinary_flag (v : (coarse).graph.Site) :
    publishedHub flag k g (splitKey (address v)).2=billed v :=
  published_flag_at_reclaimed (J:=J) (V:=V) sel key flag k g v

include oldEmpty in
omit [Fintype J₁] [DecidableEq J₁] in
theorem ordinary_empty (v : (coarse).graph.Site)
    (exterior : publishedHub flag k g (position v).2.val=true) : records v=[] := by
  apply new_hub_empty W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p inc picked oldEmpty
  exact (ordinary_flag W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p v).symm.trans exterior

include oldEmpty in
omit [Fintype J₁] in
theorem ordinary_filled (v : J₁×Host V k slots) (i : Block n)
    (atHub : publishedHub flag k g v.2.val=true) :
    blockMass (W₁).graph position block ((W₁).siteUnits billed records wire β hist) v i=2^g*U := by
  let send := fun u : W.graph.Site=>MarkedWorld.address sel key flags k g (newSite N pick lay pack (.inl u))
  have forward (u : W.graph.Site) (hu : flag (pos u).2 = true) :
      address (send u) = (pos u,(k-g,group (k-g) (ix u)),0) :=
    old_address W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
      ag gk keep filled u hu (Nat.mul_pos hs hb)
  let charge := (W₁).siteUnits billed records wire β hist
  have saturated (u : (coarse).graph.Site)
      (hu : publishedHub flag k g (splitKey (address u)).2 = true) : charge u = 2^g*U :=
    post_hub_full W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
      ag gk inc picked oldEmpty filled q counts cut (Nat.mul_pos hs hb) u
      ((ordinary_flag W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p u).symm.trans hu)
  exact complete_hub_mass N pos ix full send address digits entries flag U (Nat.mul_pos hs hb)
    gk filled forward charge saturated v i atHub

include ag gk inc picked oldEmpty filled hb hs paid birth degree adj digits in
/-- All local geometric data are constructed from the actual chosen graph.
The remaining two scalar inequalities are expressed in the old record count,
the number of picked pairs, and the preallocated group/host bounds. -/
def ordinary_successor (unit cap₁ : ℕ) (hn : 0<n) (hu : 0<unit) (cap : 0<cap₁) (hw : 0<wire)
    (hq : q=unit*G.b) (scaleEq : 2^g*U=wire*(unit*G.b)*cap₁)
    (price ε : ℝ) (pp : 0<price)
    (atomBill : price*hist*((∑u,(rec u).length)+6*Fintype.card I:ℕ)≤ε)
    (hostBill : ((Fintype.card J₁* (Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 rootDegree*(price*((2^g*U:ℕ):ℝ)))≤ε) :
    StageInput W₁ G (price*wire) ε where
  V := J₁×Host V k slots
  Atoms := Record T G.C
  k := n
  pos := position
  «block» := block
  hub := billed
  «records» := records
  wire := wire
  hist := hist
  z := unit
  cap := cap₁
  Δ := rootDegree
  near := near₁
  fieldBits := hn
  degreeMin := by
    have one : 1≤(Δ+1)*((D+g)+1+2*2^(D+g)) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have lower : 2≤(Δ+1)*((D+g)+1+2*2^(D+g))*slots := by
      calc
        2≤ slots := Nat.le_add_left 2 (2^a)
        _=1*slots := (one_mul _).symm
        _≤_ := Nat.mul_le_mul_right _ one
    exact le_trans (by decide : 2≤2^10) (Nat.pow_le_pow_left lower 10)
  degree := fun v=>(grouped_degree _ v).le.trans (restricted_degree near (D+g) k slots Δ degree v.2)
  wirePos := hw
  unitPos := hu
  capPos := cap
  small v i := (ordinary_mass W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    oldEmpty filled hb hs paid birth degree adj digits q counts cut v i).trans_eq scaleEq
  adjacent e _ := (ordinary_close W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    filled hb hs paid adj digits q counts cut e).1
  reverse e _ := (ordinary_close W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    filled hb hs paid adj digits q counts cut e).2.1
  internal e _ := (ordinary_close W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p ag gk inc picked
    filled hb hs paid adj digits q counts cut e).2.2
  widths e h := (DescentCableUnbundling.uniform (coarse).graph (coarse).core counts q e h).trans hq
  inside := (ordinary_incidence W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p inc picked q counts cut).inside
  outside := (ordinary_incidence W G pos ix near flag rec wire hist Δ B scale small sheet same z hz fit p inc picked q counts cut).outside
  q := price
  qpos := pp
  unitPrice := rfl
  retained := by
    have count := post_atom_count W G pos ix nn flags rec wire β hist 20 Δ B scale small sheet same z hz fit p
    rw [←Nat.cast_sum]
    refine le_trans (le_of_eq ?_) atomBill
    exact congrArg (fun population : ℕ => price * (hist : ℝ) * (population : ℝ)) count
  roots := by
    rw [←scaleEq,Fintype.card_prod]
    have hostCount := Nat.mul_le_mul_left (Fintype.card J₁) (host_size (V:=V) (k:=k) («slots»:=slots))
    have counted : ((Fintype.card J₁ * Fintype.card (Host V k slots) : ℕ) : ℝ) ≤
        ((Fintype.card J₁ * (Fintype.card V * 2^(k+1) * slots) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hostCount
    have tariffNonnegative : 0 ≤ (2:ℝ)^packExponent 20 rootDegree * (price * ((2^g*U:ℕ):ℝ)) := by positivity
    exact (mul_le_mul_of_nonneg_right counted tariffNonnegative).trans hostBill

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
