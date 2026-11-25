import OAI.Hierarchy.DescentGroupStage
import OAI.Hierarchy.DescentGroupedAffineScore
import OAI.Hierarchy.DescentRosterMeasured
import OAI.Hierarchy.DescentScheduledBitHistory

namespace OAI
/-! # The canonical ordinary shrink over many groups sharing a single host -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open WinningSlabs
open scoped Classical BigOperators
noncomputable section
variable {C L k ℓ Δ d : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k)

def groupedCounts (ej : J≃Fin C) (ev : V≃Fin L) (weight : W.graph.Site→ℕ) (g : Fin C) (v : Fin L) :=
  blockMass W.graph A.pos A.block weight (ej.symm g,ev.symm v)

def namedRank (ej : J≃Fin C) (ev : V≃Fin L) : J×V ≃ Fin (C*L) :=
  (ej.prodCongr ev).trans (GroupedScan.product C L)

def lifted (inc : V→List V) (z : J×V) : List (J×V) := (inc z.2).map (liftSite z.1)

theorem lifted_listed (inc : V→List V) (listed : ∀v z,v∈inc z ↔ z∈A.near v) (i j : J×V) :
    i∈lifted inc j ↔ j∈groupedNear A.near i := by
  change i∈(inc j.2).map (liftSite j.1) ↔ j∈(A.near i.2).map (liftSite i.1)
  constructor
  · intro hit
    obtain ⟨v,mem,rfl⟩ := List.mem_map.mp hit
    exact Finset.mem_map.mpr ⟨j.2,(listed v j.2).mp mem,Prod.eta j⟩
  · intro hit
    obtain ⟨z,mem,rfl⟩ := Finset.mem_map.mp hit
    exact List.mem_map.mpr ⟨i.2,(listed i.2 z).mpr mem,Prod.eta i⟩

omit [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem named_neighbors (ej : J≃Fin C) (ev : V≃Fin L) (inc : V→List V) :
    (fun t=>(lifted inc ((namedRank ej ev).symm t)).map (namedRank ej ev)) =
      GroupedScan.neighbors C (fun i=>(inc (ev.symm i)).map ev) := by
  funext t
  obtain ⟨⟨g,v⟩,rfl⟩ := (namedRank ej ev).surjective t
  rw [Equiv.symm_apply_apply]
  change ((inc v).map (liftSite g)).map (namedRank ej ev) =
    GroupedScan.neighbors C (fun i=>(inc (ev.symm i)).map ev) (GroupedScan.site (ej g) (ev v))
  simp only [GroupedScan.neighbor_site,Equiv.symm_apply_apply,List.map_map]; rfl

theorem named_counts (ej : J≃Fin C) (ev : V≃Fin L) (f : W.graph.Site→ℕ) :
    (fun v=>blockMass W.graph A.pos A.block f ((namedRank ej ev).symm v)) =
      GroupedScan.flat (A.groupedCounts ej ev f) := by
  funext v
  rfl

local notation "fee" => A.wire*(A.z*G.b)
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "D" => DescentHostDegree.gap A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v=>A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v : W.graph.Site=>Finset.card (Finset.filter (fun edge=>W.graph.src edge=v) W.core)

/-- From the literal first minima of the grouped, padded schedule recover the
particular graph, filling and port assignment of the unpadded measured history.
The only duplicated semantic index is the load group. All groups read the
same single host-neighbor directory. -/
theorem grouped_named (he : 0≤ε) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
    (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (μ : Nonzero k) (j : Candidate k)
    (seed :
      let Q := uniformColonyScore (DynamicSplit.incoming rs)
        (fun g=>Padded.table (A.groupedCounts ej ev full g)) D cap (modulus A.fieldBits)
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ))
    (paint :
      let S := GroupedScan.groupedSlabs (DynamicSplit.incoming rs)
        (fun g=>Padded.table (A.groupedCounts ej ev full g)) (fun g=>Padded.table (A.groupedCounts ej ev outgoing g))
        D cap (modulus A.fieldBits) μ
      (scanMinimum (scoreAt S) (List.range (2^(k+1)))).1=some (j.val,score S j)) :
    IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
      (groupedNear A.near) A.fieldBits A.small (A.stage.result he) μ (linear j) (offset j) ∧
      μ=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β := by
  let N := DynamicSplit.compact rs h
  let inc := fun z=>(N (ev z)).map ev.symm
  let rank := namedRank ej ev
  let income := fun t => (lifted inc (rank.symm t)).map rank
  let weighted := A.groupedCounts ej ev full
  let amounts := A.groupedCounts ej ev outgoing
  obtain ⟨padded,source,re⟩:=DynamicSplit.unpack_roster rs h ev A.near members
  change DynamicSplit.incoming rs = Padded.neighbors h N at padded
  change (fun i => (inc (ev.symm i)).map ev) = N at re
  have liftedSource := A.lifted_listed inc source
  have table : income=GroupedScan.neighbors C N :=
    (named_neighbors ej ev inc).trans (congrArg (GroupedScan.neighbors C) re)
  have ww : A.stage.loadsAt rank=(fun _ : Fin 1=>GroupedScan.flat weighted) :=
    funext fun _=>A.named_counts ej ev full
  have oo : A.stage.outgoingAt rank=(fun _ : Fin 1=>GroupedScan.flat amounts) :=
    funext fun _=>A.named_counts ej ev outgoing
  let cost := fun ν:Nonzero k=>colonyCount (fun _ : Unit=>blockMass W.graph A.pos A.block full)
    (fun v z=>z∈groupedNear A.near v) a (fee*A.cap) A.degree (fun _=>A.small) (multiplier A.fieldBits ν)
  have canonical : uniformColonyScore N weighted D cap (modulus A.fieldBits)=cost := by
    funext ν
    have eqn : uniformColonyScore income (A.stage.loadsAt rank) D cap (modulus A.fieldBits) ν = cost ν :=
      A.stage.score_is_canonical rank (lifted inc) liftedSource ν
    rw [table,ww] at eqn
    exact (GroupedScan.uniform_score N weighted D cap (modulus A.fieldBits) ν).symm.trans eqn
  let r:=DescentKernelHistory.BitDescription.scannedRows he A.stage
  have old:=r.native
  have first:=r.firstPaint
  have chosenSeed : (scanMinimum cost (nonzeroWords k)).1 = some (r.μ,cost r.μ) := old.1
  have found := Padded.same_multiplier h N weighted D cap (modulus A.fieldBits) (nonzeroWords k)
  rw [←padded,seed,canonical,chosenSeed] at found
  have sameSeed : μ=r.μ := Option.some.inj found
  subst μ
  let m := multiplier A.fieldBits r.μ
  let orig := affineDirectory W.graph W.core A.pos (reindexedBlock W.graph A.block m) full (groupedNear A.near)
    D a A.cap fee (small_reindexed W.graph A.pos A.block full A.small m)
  let S := GroupedScan.groupedSlabs (DynamicSplit.incoming rs) (fun g=>Padded.table (weighted g))
    (fun g=>Padded.table (amounts g)) D cap (modulus A.fieldBits) r.μ
  have all (q : Candidate k) : score S q=score orig q := by
    have eqn : score (worldValue
        (Selected.winningRows income (A.stage.loadsAt rank) D cap (modulus A.fieldBits) r.μ)
        (Selected.winningAmounts (A.stage.outgoingAt rank) (modulus A.fieldBits) r.μ)) q =
        score orig q := A.stage.affine_is_canonical rank (lifted inc) liftedSource r.μ q
    rw [table,ww,oo] at eqn
    dsimp only [S]
    rw [padded]
    exact (Padded.slab_score h N weighted amounts D cap (modulus A.fieldBits) r.μ q).trans
      ((GroupedScan.slab_score N weighted amounts D cap (modulus A.fieldBits) r.μ q).symm.trans eqn)
  have objective : scoreAt S=scoreAt orig := by
    funext i
    unfold scoreAt
    split <;> first | apply all | rfl
  have observed : FirstPaint W.graph W.core A.pos (reindexedBlock W.graph A.block m) full (groupedNear A.near)
      D a A.cap fee (small_reindexed W.graph A.pos A.block full A.small m) j := by
    change (scanMinimum (scoreAt orig) _).1=some (j.val,score orig j)
    simpa only [objective,all] using (show (scanMinimum (scoreAt S) _).1=some (j.val,score S j) from paint)
  have same := firstPaint_unique _ _ _ _ _ _ _ _ _ _ _ observed first
  have slope : linear j = r.α :=
    (congrArg (linear (k:=k)) same).trans (linear_code r.α r.β)
  have bias : offset j = r.β :=
    (congrArg (offset (k:=k)) same).trans (offset_code r.α r.β)
  refine ⟨?_,rfl,same⟩
  rw [slope,bias]
  exact old

theorem grouped_scanned (he : 0≤ε) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
    (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (μ : Nonzero k) (j : Candidate k)
    (seed :
      let Q := uniformColonyScore (DynamicSplit.incoming rs)
        (fun g=>Padded.table (A.groupedCounts ej ev full g)) D cap (modulus A.fieldBits)
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ))
    (paint :
      let S := GroupedScan.groupedSlabs (DynamicSplit.incoming rs)
        (fun g=>Padded.table (A.groupedCounts ej ev full g)) (fun g=>Padded.table (A.groupedCounts ej ev outgoing g))
        D cap (modulus A.fieldBits) μ
      (scanMinimum (scoreAt S) (List.range (2^(k+1)))).1=some (j.val,score S j)) :
    IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
      (groupedNear A.near) A.fieldBits A.small (A.stage.result he) μ (linear j) (offset j) :=
  (A.grouped_named he ej ev h rs members μ j seed paint).1

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
