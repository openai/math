import OAI.Hierarchy.DescentNormalizationNames
import OAI.Hierarchy.DescentOrdinaryVenueRows
import OAI.Hierarchy.DescentOrdinaryHubRows
import OAI.Hierarchy.DescentOrdinaryParticleReceipt
import OAI.Hierarchy.DescentCutAlignment
import OAI.Hierarchy.DescentGroupedSuccessor
import OAI.Hierarchy.DescentCalendarGroupedStage
import OAI.Hierarchy.DescentPickedAtomCount
import OAI.Hierarchy.DescentIssuedNodeOrder

namespace OAI
/-! # The next grouped placement and retained scalar description on every actual profile -/

namespace Hierarchy.DescentSixParty.GroupStage
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentGL DescentWalshTables
open StarKeys GadgetNetwork MarkedWorld DescentHostDegree DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {P : Type} {d k n : ℕ} {bits : P→ℕ} {F : Type} [Field F]
variable {G : PoweredGadget F} {W : MarkedWorld F d P bits} {ε price : ℝ}
variable {J J₁ V : Type} [Fintype J] [Fintype J₁] [Fintype V] [DecidableEq J] [DecidableEq J₁] [DecidableEq V]
variable (A : GroupStage W G price ε J V k)
local notation "a" => packExponent 20 A.degree
local notation "g" => gainExponent 20 A.degree
local notation "window" => gap A.degree+g
local notation "slots" => (2^a+2)
local notation "nextDegree" => (((A.degree+1)*(window+1+2^window)*slots)^10)
local notation "unit" => A.wire*(A.z*G.b)
local notation "U" => unit*A.cap

private theorem subround_all_widths_dvd
    {I C H : Type} [Fintype I] [DecidableEq H]
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I × Fin 2 ↪ W.graph.Edge) (z : I → ℕ) (hz : ∀ i, 0 < z i)
    (fit : ∀ i s, W.graph.width (pick (i, s)) = z i * G.b)
    (pack : W.graph.Site → C) (p : I → Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site ↪ Key H)
    (flag : H → Bool) (level gain quantum : ℕ)
    (old : ∀ e ∈ W.core, quantum ∣ W.graph.width e) (picked : ∀ j, pick j ∈ W.core)
    (chunks : ∀ i, quantum ∣ z i) (allOld : ∀ e, quantum ∣ W.graph.width e) :
    ∀ e, quantum ∣
      (subroundNormalize W G pick z hz fit pack p key flag level gain quantum old picked chunks).result.graph.width e := by
  have selectedWidth : ∀ e : (W.selected G pick z hz fit pack p).graph.Edge,
      quantum ∣ (W.selected G pick z hz fit pack p).graph.width e := by
    rintro ⟨raw, _⟩
    rcases raw with prev | (arm | wire)
    · exact allOld prev
    · exact allOld (pick arm)
    · exact dvd_mul_of_dvd_left (chunks wire.1) _
  intro e
  rcases e with retained | piece
  · exact selectedWidth retained.val.val
  · exact dvd_rfl


set_option maxHeartbeats 1200000 in
/-- Per-profile state and semantics follow the true finite multiplier scan.
The scalar allowance concerns only the old graph, public population and
age-dependent rate. In particular no new graph, tensor, or hub cap is supplied. -/
theorem scanned_geometry_issued_particles (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (ParticleRows hε A.stage c _ norm (fun v=>(next.records v).length) (fun v=>next.hub (next.pos v).2) ∧
          HubRows A hε digits next (Function.Embedding.subtype _) ∧
          VenueRows A hε A.stage c digits norm next (Function.Embedding.subtype _) ∧
          (∀v,next.hub v=publishedHub A.hub k g v.val) ∧
          next.near=restrictedNear A.near window k slots ∧ norm.nameCount=0) ∧
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
            DescentStageEdgeReceipt.IssuedRows hε A.stage c oldOrder
              (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape pair) ∧
        Normalize.CutsEqual A.z norm ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  let rows := DescentKernelHistory.BitDescription.scannedRows hε A.stage
  let μ := rows.μ
  let α := rows.α
  let β := rows.β
  let fit := rows.fit
  let N := W.graph
  let L := multiplier A.fieldBits μ
  let ix := reindexedBlock N A.block L
  let flags := fun v : J×V=>A.hub v.2
  let measure := W.siteUnits (flags∘A.pos) A.records A.wire 256 A.hist
  let small := small_reindexed N A.pos A.block measure A.small L
  let sheet := fun i : Block k=>decide (binaryRow α ((address k).symm i)+β=0)
  let home := occupiedHome N A.pos ix measure (groupedNear A.near) (gap A.degree) a U small
  let col := occupiedAddress N U (groupedNear A.near) (gap A.degree) a (blockMass N A.pos ix measure) small A.pos ix
  let I := NativePair N W.core home (sheet∘ix) A.cap
  let pick := colorPick N W.core home (sheet∘ix) A.cap
  let pack := coloredPack N W.core home (sheet∘ix) A.cap
  let p : I→Profile G.C := rows.profile c
  have eqState : (A.stage.result hε).state c=W.selected G pick (fun _=>A.z) (fun _=>A.unitPos) fit pack p := rows.state c
  rw [eqState]
  have aligned (e : N.Edge) : ix (N.src e)=ix (N.dst e) := congrArg (rearrange L) (A.same e)
  let key := nativeKey N W.core home (sheet∘ix) A.cap col
    (fun e _=>congrArg sheet (aligned e)) (bestLayout (branchWidth G (fun _=>A.z) p))
  have picked : ∀ j, pick j ∈ W.core := rows.picked
  have div : ∀e∈W.core,A.z∣N.width e := fun e h=>A.widths e h ▸ dvd_mul_right A.z G.b
  let rep := repetitions W G pick (fun _=>A.z) (fun _=>A.unitPos) fit pack p key flags k g A.z
  let cut := repetition_width W G pick (fun _=>A.z) (fun _=>A.unitPos) fit pack p key flags k g A.z div picked (fun _=>dvd_rfl)
  let step := subroundNormalize W G pick (fun _=>A.z) (fun _=>A.unitPos) fit pack p key flags k g A.z div picked (fun _=>dvd_rfl)
  have allFull (v : J×V) (yes : flags v=true) (j : Block k) : blockMass N A.pos ix measure v j=U := by
    rw [show blockMass N A.pos ix measure=rearrangedLoad (blockMass N A.pos A.block measure) L from blockMass_reindexed ..]
    exact A.saturated v yes _
  have base : 0<G.b := by have := G.paid;omega
  have volume : 0<A.z*G.b := Nat.mul_pos A.unitPos base
  have pairBound := paired_count_le W pick picked A.z G.b volume fit
  have atomPaid : price*A.hist*((∑u,(A.records u).length)+6*Fintype.card I:ℕ)≤ε := by
    apply le_trans _ oldLedger
    apply mul_le_mul_of_nonneg_left _ (by have := A.pricePos;positivity)
    exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left 6 pairBound) _
  let cap := 2^g*G.b*A.cap
  have scale : 2^g*U=A.wire*(newZ*G.b)*cap := by
    change 2^g*(A.wire*(A.z*G.b)*A.cap)=A.wire*(newZ*G.b)*(2^g*G.b*A.cap)
    rw [←grain]
    ring
  -- The unrestricted directory estimate also pays for all intermediate slots.
  -- Construct its geometry and then pay only for distinct reachable addresses.
  let directoryDegree := ((A.degree+1)*(window+1+2*2^window)*slots)^10
  let directoryBill := ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
    ((2:ℝ)^packExponent 20 directoryDegree*(price*((2^g*U:ℕ):ℝ)))
  let geometry : GroupStage step.result G price (max ε directoryBill) J₁ (Host V k slots) n :=
    ordinary_group W G A.pos ix A.near A.hub A.records A.wire A.hist A.degree A.cap unit small sheet aligned
    (fun _=>A.z) (fun _=>A.unitPos) fit p ag gk A.incidence picked A.noHubAtoms allFull A.capPos
    (Nat.mul_pos A.wirePos volume) (fun e h=>by rw [A.widths e h])
    (fun i j => histCost.trans_eq (congrArg (fun width : ℕ => A.wire * width) (fit i j).symm)) A.degreeBound A.peers digits A.z rep cut
    newZ cap hn hz₁ (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos g) base) A.capPos) A.wirePos grain scale price (max ε directoryBill)
    A.pricePos (atomPaid.trans (le_max_left _ _)) (le_max_right _ _)
  have population := post_atom_count W G A.pos ix (groupedNear A.near) flags A.records A.wire 256 A.hist 20
    A.degree A.cap unit small sheet aligned (fun _=>A.z) (fun _=>A.unitPos) fit p
  have actualRecordBill : price*geometry.hist*((∑ v,(geometry.records v).length:ℕ):ℝ)≤ε :=
    (congrArg (fun number : ℕ => price*(A.hist:ℝ)*(number:ℝ)) population).le.trans atomPaid
  have finalSlots : 3 ≤ slots := by have positive := Nat.two_pow_pos a; omega
  let next : GroupStage step.result G price ε J₁ (Host V k slots) n :=
    geometry.withCalendarDegree A.near window A.degree A.degreeBound rfl finalSlots ε actualRecordBill
    (by change _ * ((2:ℝ)^packExponent 20 nextDegree*(price*((A.wire*(newZ*G.b)*cap:ℕ):ℝ))) ≤ ε
        rw [←scale]
        exact rootLedger)

  let cellRank := DescentStageEdgeReceipt.groupRank groupID vertex
  have colOk (ci : _) : DescentStageEdgeReceipt.thickKey (col ci)∈keys k 1 :=
    DescentStageEdgeReceipt.nativeAddress_legal hε A.stage ci
  let cr := DescentPacking.originalId (DescentStageEdgeReceipt.ScanColonies hε A.stage)
  let pairOrd := DescentPacking.PairRAM.globalNumberBy N W.core home (sheet∘ix) A.cap cr
  let tape := DescentStageEdgeReceipt.ordinary W G oldOrder pairOrd pick (fun _=>A.z) (fun _=>A.unitPos)
    fit pack p key flags k g A.z div picked (fun _=>dvd_rfl)
  have rawFlag := ordinary_flag W G A.pos ix A.near A.hub A.records A.wire A.hist A.degree A.cap unit small sheet aligned
    (fun _=>A.z) (fun _=>A.unitPos) fit p
  have actualTag : (fun v : step.result.graph.Site => next.hub (next.pos v).2) =
      (fun v : step.result.graph.Site => A.hub v.val.1.2) := by
    funext v
    change publishedHub A.hub k g (splitKey v.val).2 = A.hub v.val.1.2
    exact rawFlag v
  have packedTags := scanned_pack_flags W A.pos ix (groupedNear A.near) flags A.records A.wire 256 A.hist 20
    A.degree A.cap unit small sheet
  have chosenTags := scanned_hub_flags W G A.pos ix (groupedNear A.near) flags A.records A.wire 256 A.hist 20
    A.degree A.cap unit small sheet aligned (fun _=>A.z) (fun _=>A.unitPos) fit p A.incidence picked
  have nativeRows := ParticleRows.stage (W := W) (G := G) (he := hε) (T := A.stage) (c := c) (V := J × V)
    key flags A.pos rfl k g A.z div picked (fun _ => dvd_rfl) A.incidence packedTags chosenTags
  have localRows : ParticleRows hε A.stage c _ step (fun v=>(next.records v).length) (fun v=>next.hub (next.pos v).2) := by
    apply (congrArg (fun f : step.result.graph.Site → Bool =>
      ParticleRows hε A.stage c _ step (fun v => (next.records v).length) f) actualTag).mpr
    exact nativeRows
  have pinRows : HubRows A hε digits next (Function.Embedding.subtype _) := by
    intro pin flag
    let v:=(step.result).graph.attach pin
    let e:=StarKeys.attachment_forward W G A.pos ix (groupedNear A.near) flags A.records A.wire 256 A.hist 20
      A.degree A.cap unit small sheet aligned (fun _=>A.z) (fun _=>A.unitPos) fit p ag gk
      (fun i=>(A.incidence.inside _ (picked (i,1))).1) allFull
      (Nat.mul_pos (Nat.mul_pos A.wirePos volume) A.capPos) pin flag
    change v.val=(A.pos (N.attach pin),(k-g,group (k-g) (ix (N.attach pin))),0) at e
    change ((digits (splitKey v.val).1).1,(digits (splitKey v.val).1).2)=digits (A.pos (N.attach pin)).1 ∧
      (splitKey v.val).2=((A.pos (N.attach pin)).2,(k-g,group (k-g) (ix (N.attach pin))),0)
    rw [e]
    exact ⟨rfl,rfl⟩
  have keyRoom (v : _) : key v∈keys k slots :=
    selected_address W G A.pos ix (groupedNear A.near) flags A.records A.wire 256 A.hist 20 A.degree A.cap unit
      small sheet aligned (fun _=>A.z) (fun _=>A.unitPos) fit p A.capPos (Nat.mul_pos A.wirePos volume)
      (by decide) (fun e h=>by rw [A.widths e h]) v
  have homeReads (v : N.Site) : HEq (col (home v)).1 (A.stage.pos v) ∧ flags (col (home v)).1=A.stage.hub v := by
    rw [show col (home v)=_ from occupiedAddress_colonyOf N U (groupedNear A.near) (gap A.degree) a
      (blockMass N A.pos ix measure) small A.pos ix v]
    exact ⟨HEq.rfl,rfl⟩
  let actualChart : DescentStageEdgeReceipt.IssuedDonorChart hε A.stage (J×V) :=
    ⟨col,(fun e _=>congrArg sheet (aligned e)),flags,HEq.rfl,(fun _=>rfl),homeReads⟩
  have venueRows : VenueRows A hε A.stage c digits step next (Function.Embedding.subtype _) := by
    intro state b x
    let curr:=GadgetNetwork.newSite N pick (bestLayout (branchWidth G (fun _=>A.z) p)) pack x
    have agrees := actualChart.merged_agree b c k g curr
    exact ⟨congrArg (fun address : Key (J × V) => digits (splitKey address).1) agrees,
      congrArg (fun address : Key (J × V) => (splitKey address).2) agrees⟩
  have issuedTape : DescentStageEdgeReceipt.IssuedRows hε A.stage c oldOrder cellRank _ step tape pairOrd :=
    DescentStageEdgeReceipt.IssuedRows.stage (W := W) (G := G) (he := hε) (T := A.stage)
      (choice := c) (oldID := oldOrder) (rootRank := cellRank) (H := J × V) col
      (fun e _=>congrArg sheet (aligned e)) flags k g A.z colOk ⟨⟨cellRank,HEq.rfl,rfl⟩,rfl,rfl,keyRoom,HEq.rfl,(fun _=>rfl),homeReads⟩ div picked (fun _=>dvd_rfl)
  refine ⟨step,next,⟨localRows,pinRows,venueRows,(fun _=>rfl),rfl,rfl⟩,⟨tape,pairOrd,issuedTape⟩,⟨rfl,trivial⟩,next_injective _ digits _,rfl,rfl,rfl,rfl,rfl,?_,Fintype.card I,?_,?_⟩
  · intro oldUnits e
    change newZ*G.b ∣ (step.result).graph.width e
    rw [←grain]
    exact subround_all_widths_dvd W G pick (fun _ => A.z) (fun _ => A.unitPos)
      fit pack p key flags k g A.z div picked (fun _ => dvd_rfl)
      (fun edge => (dvd_mul_right A.z G.b).trans (oldUnits edge)) e
  · exact population
  · have bound := paired_count_width (I := I) W pick picked A.z G.b fit
    calc
      2 * Fintype.card I * (A.z * G.b) = Fintype.card I * (2 * (A.z * G.b)) := by ac_rfl
      _ ≤ W.liveWidth := bound

theorem scanned_geometry_issued_rows (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
            DescentStageEdgeReceipt.IssuedRows hε A.stage c oldOrder
              (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape pair) ∧
        Normalize.CutsEqual A.z norm ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  obtain ⟨norm,next,_,rest⟩ := A.scanned_geometry_issued_particles hε digits hn ag gk newZ hz₁ grain histCost oldLedger
    rootLedger oldOrder groupID vertex c
  exact ⟨norm,next,rest⟩

theorem scanned_geometry_order (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          DescentStageEdgeReceipt.Issued W G oldOrder (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape) ∧
        Normalize.CutsEqual A.z norm ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  obtain ⟨norm,next,⟨tape,pair,receipt⟩,remaining⟩ :=
    A.scanned_geometry_issued_rows hε digits hn ag gk newZ hz₁ grain histCost oldLedger rootLedger
      oldOrder groupID vertex c
  exact ⟨norm,next,⟨tape,receipt.toIssued⟩,remaining⟩

theorem scanned_geometry (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  let raw := (Fintype.equivFin W.graph.Edge).toEmbedding
  let groups := (Fintype.equivFin J).toEmbedding.trans Fin.valEmbedding
  let vertices := (Fintype.equivFin V).toEmbedding.trans Fin.valEmbedding
  obtain ⟨norm,next,_,_,_,good⟩ := A.scanned_geometry_order hε digits hn ag gk newZ hz₁ grain histCost
    oldLedger rootLedger raw groups vertices c
  exact ⟨norm,next,good⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
