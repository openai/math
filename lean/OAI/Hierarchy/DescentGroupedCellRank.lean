import OAI.Hierarchy.DescentGroupedMeasuredPaint
import OAI.Hierarchy.DescentMeasuredCellRank

namespace OAI
/-! # The relative winning-cell ordinal of each old site using a shared host roster -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentGL DescentBinaryField DescentHostDirectory StarKeys WinningSlabs
open scoped Classical BigOperators
noncomputable section
variable {C L k ℓ Δ d : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
variable (rs : DynamicSplit.Roster ℓ Δ)
variable (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
variable (μ : Nonzero k)
local notation "fee" => A.wire*(A.z*G.b)
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "D" => DescentHostDegree.gap A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v=>A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "blk" => reindexedBlock W.graph A.block (multiplier A.fieldBits μ)
local notation "mass" => blockMass W.graph A.pos blk full
local notation "fit" => small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits μ)
local notation "home" => occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
local notation "whereAt" => occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a mass fit A.pos blk
local notation "counts" => A.groupedCounts ej ev full
local notation "rows" => Selected.winningRows (DynamicSplit.incoming rs) (fun g=>Padded.table (counts g)) D cap (modulus A.fieldBits) μ

include members in
theorem grouped_cell_depth (v : J×V) (x : Block k) :
    Scan.leafDepth (rows (ej v.1)) ((ev v.2).castLE h) x=depthAt (fee*A.cap) (groupedNear A.near) D a mass fit v x := by
  let N:=DynamicSplit.compact rs h
  let inc:=fun z=>(N (ev z)).map ev.symm
  let rank:=namedRank ej ev
  let f:=modulus A.fieldBits
  obtain ⟨padded,listed,re⟩:=DynamicSplit.unpack_roster rs h ev A.near members
  change DynamicSplit.incoming rs = Padded.neighbors h N at padded
  change (fun i => (inc (ev.symm i)).map ev) = N at re
  have table : (fun t=>(lifted inc (rank.symm t)).map rank)=GroupedScan.neighbors C N :=
    (named_neighbors ej ev inc).trans (congrArg (GroupedScan.neighbors C) re)
  have move : multiplierLoad (GroupedScan.flat counts) f μ.val=fun t=>mass (rank.symm t) := by
    rw [←A.named_counts ej ev full]
    have load := (multiplierLoad_eq (blockMass W.graph A.pos A.block full) f μ.val
      (multiplier A.fieldBits μ) (multiplier_native A.fieldBits μ)).trans
      (blockMass_reindexed W.graph A.pos A.block full (multiplier A.fieldBits μ)).symm
    funext t y
    exact congrFun (congrFun load (rank.symm t)) y
  have posD : 0<D := by
    have pow := Nat.le_pow_clog (by decide : 1<2) (2*A.degree)
    have lower:=A.degreeMin
    unfold DescentHostDegree.gap DescentHostDegree.logDegree
    by_contra! zero
    have bad : Nat.clog 2 (2*A.degree)=0 := by omega
    rw [bad,pow_zero] at pow
    omega
  calc
    _ = Scan.leafDepth (Scan.build N (multiplierLoad (counts (ej v.1)) f μ.val) D cap k) (ev v.2) x := by
      change Scan.leafDepth (Scan.build (DynamicSplit.incoming rs) (multiplierLoad (Padded.table (counts (ej v.1))) f μ.val)
        D cap k) (Padded.front h (ev v.2)) x=_
      rw [padded]
      unfold Scan.leafDepth
      simp_rw [Scan.padded_lookup (Padded.front h) N (Padded.neighbors h N)
        (multiplierLoad (counts (ej v.1)) f μ.val) _ (Padded.live_neighbors h N) (Padded.live_weight h _ f μ.val)]
    _ = Scan.leafDepth (Scan.build (GroupedScan.neighbors C N) (multiplierLoad (GroupedScan.flat counts) f μ.val)
        D cap k) (rank v) x := by
      change _=Scan.leafDepth _ (GroupedScan.site (ej v.1) (ev v.2)) x
      unfold Scan.leafDepth
      simp_rw [GroupedScan.split_at N counts D cap f μ.val (ej v.1) k]
    _ = Scan.leafDepth (Scan.build (lifted inc) mass D cap k) v x := by
      rw [move,←table]
      unfold Scan.leafDepth
      simp_rw [Scan.lookup_reindex rank (lifted inc) mass D cap]
    _ = _ := Scan.leafDepth_eq (lifted inc) (fun z v=>v∈groupedNear A.near z) (A.lifted_listed inc listed)
      mass posD a (fee*A.cap) fit v x

include members in
/-- The decoded occupied site keeps its group and host and the dyadic cell of the
native shared-host winning rows, evaluated at the relocated original block. -/
theorem grouped_cell_at (x : W.graph.Site) :
    let rx:=blk x
    let z:=Scan.leafDepth (rows (ej (A.pos x).1)) ((ev (A.pos x).2).castLE h) rx
    whereAt (home x)=(A.pos x,(z,group z rx)) := by
  dsimp only
  rw [grouped_cell_depth A ej ev h rs members μ (A.pos x) (blk x)]
  exact occupiedAddress_colonyOf ..

include members in
/-- The physical label comprises the group ordinal, the live row of the padded
common host, and the relative binary-heap ordinal written at that row. -/
theorem grouped_cell_words (x : W.graph.Site) :
    let addr:=whereAt (home x)
    let rx:=blk x
    let z:=Scan.leafDepth (rows (ej (A.pos x).1)) ((ev (A.pos x).2).castLE h) rx
    ((ej addr.1.1).val,(ev addr.1.2).val,2^addr.2.1-1+addr.2.2)=
      ((ej (A.pos x).1).val,((ev (A.pos x).2).castLE h).val,2^z-1+group z rx) := by
  dsimp only
  rw [grouped_cell_at A ej ev h rs members μ x]; rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
