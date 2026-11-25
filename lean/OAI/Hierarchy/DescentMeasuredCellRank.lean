import OAI.Hierarchy.DescentRosterMeasured

namespace OAI
/-! # The occupied-cell numbers read at the genuine padded winning rows -/

namespace Hierarchy.DescentSixParty.StageInput
open DescentColonies DescentGL DescentBinaryField DescentPacking StarKeys WinningSlabs
open scoped Classical
noncomputable section

private def heapKey (a : ℕ×ℕ) := 2^a.1-1+a.2

private theorem heapKey_before {x y : ℕ×ℕ} (hx : x.2<2^x.1) (earlier : x.1<y.1) :
    heapKey x<heapKey y := by
  have powers : 2^(x.1+1)≤2^y.1 := Nat.pow_le_pow_right (by decide) earlier
  rw [pow_succ] at powers
  have := Nat.two_pow_pos x.1
  unfold heapKey
  omega

private theorem heapKey_inj {x y : ℕ×ℕ} (hx : x.2<2^x.1) (hy : y.2<2^y.1)
    (eqn : heapKey x=heapKey y) : x=y := by
  have same : x.1=y.1 := by
    rcases lt_trichotomy x.1 y.1 with h|h|h
    · exact False.elim ((Nat.ne_of_lt (heapKey_before hx h)) eqn)
    · exact h
    · exact False.elim ((Nat.ne_of_lt (heapKey_before hy h)) eqn.symm)
  apply Prod.ext same
  unfold heapKey at eqn
  rw [same] at eqn
  omega

variable {F P : Type} [Field F] {d L ℓ Δ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {u ε : ℝ} (T : StageInput W G u ε)
variable (e : T.V≃Fin L) (h : L≤2^ℓ) (μ : Nonzero T.k)
local notation "full" => W.siteUnits T.hub T.records T.wire 256 T.hist
local notation "unit" => (T.wire*(T.z*G.b))
local notation "a" => DescentHostDegree.packExponent 20 T.Δ
local notation "D" => DescentHostDegree.gap T.Δ
local notation "cap" => (2^a*(unit*T.cap))
local notation "blk" => reindexedBlock W.graph T.block (multiplier T.fieldBits μ)
local notation "mass" => blockMass W.graph T.pos blk full
local notation "fit" => small_reindexed W.graph T.pos T.block full T.small (multiplier T.fieldBits μ)
local notation "home" => occupiedHome W.graph T.pos blk full T.near D a (unit*T.cap) fit
local notation "Col" => occupied W.graph (unit*T.cap) T.near D a mass fit T.pos blk
local notation "whereAt" => occupiedAddress W.graph (unit*T.cap) T.near D a mass fit T.pos blk

private theorem cell_region_range (c : Col) : (whereAt c).2.1≤T.k ∧ (whereAt c).2.2<2^(whereAt c).2.1 := by
  obtain ⟨x,rfl⟩ := colonyOf_surjective W.graph (unit*T.cap) T.near D a mass fit T.pos blk c
  rw [occupiedAddress_colonyOf]
  let dep := depthAt (unit*T.cap) T.near D a mass fit (T.pos x) (blk x)
  have small : dep≤T.k := (depth_le ..).trans (Nat.sub_le ..)
  exact ⟨small,DescentHostDirectory.group_lt small _⟩

private def cellRegion (c : Col) : Fin (2^(T.k+1)) :=
  ⟨heapKey (whereAt c).2,by
    obtain ⟨depth,grouped⟩ := cell_region_range T μ c
    have less := heapKey_before (x:=(whereAt c).2) (y:=(T.k+1,0)) grouped (Nat.lt_succ_of_le depth)
    exact less.trans_le (Nat.sub_le (2^(T.k+1)) 1)⟩

/-- A concrete name retains the padded host row and the binary-heap rank of its occupied dyadic cell. -/
def cellEmbedding : Col ↪ Fin (2^ℓ*2^(T.k+1)) where
  toFun c := finProdFinEquiv (Padded.front h (e (whereAt c).1),cellRegion T μ c)
  inj' := by
    intro c b eqn
    have both : (Padded.front h (e (whereAt c).1),cellRegion T μ c) =
        (Padded.front h (e (whereAt b).1),cellRegion T μ b) := finProdFinEquiv.injective eqn
    apply (whereAt).injective
    apply Prod.ext
    · exact e.injective ((Padded.front h).injective (congrArg Prod.fst both))
    · exact heapKey_inj (cell_region_range T μ c).2 (cell_region_range T μ b).2
        (congrArg (fun t : Fin (2^ℓ)×Fin (2^(T.k+1)) => t.2.val) both)

private theorem embedding_value (c : Col) :
    (T.cellEmbedding e h μ c).val=(e (whereAt c).1).val*2^(T.k+1)+heapKey (whereAt c).2 := by
  change heapKey (whereAt c).2+2^(T.k+1)*(e (whereAt c).1).val=_
  ring

variable (rs : DynamicSplit.Roster ℓ Δ)
variable (members : ∀i j,j∈DynamicSplit.incoming rs i ↔
  ∃v w:T.V,i=(e v).castLE h ∧ j=(e w).castLE h ∧ v∈T.near w)
local notation "rows" => Selected.winningRows (DynamicSplit.incoming rs)
  (fun g=>Padded.table (T.loadsAt e g)) D cap (modulus T.fieldBits) μ 0

include members in
private theorem scanned_depth (v : T.V) (x : Block T.k) :
    Scan.leafDepth rows ((e v).castLE h) x=depthAt (unit*T.cap) T.near D a mass fit v x := by
  let raw := DynamicSplit.compact rs h
  let inc := fun z:T.V=>(raw (e z)).map e.symm
  obtain ⟨padded,listed,reindex⟩ := DynamicSplit.unpack_roster rs h e T.near members
  change DynamicSplit.incoming rs = Padded.neighbors h raw at padded
  change (fun i => (inc (e.symm i)).map e) = raw at reindex
  let wt := T.loadsAt e 0
  let f := modulus T.fieldBits
  have move : multiplierLoad wt f μ.val=fun t=>mass (e.symm t) := by
    have load := (multiplierLoad_eq (blockMass W.graph T.pos T.block full) f μ.val
      (multiplier T.fieldBits μ) (multiplier_native T.fieldBits μ)).trans
      (blockMass_reindexed W.graph T.pos T.block full (multiplier T.fieldBits μ)).symm
    funext t i
    exact congrFun (congrFun load (e.symm t)) i
  have posD : 0<D := by
    have pow := Nat.le_pow_clog (by decide : 1<2) (2*T.Δ)
    have lower := T.degreeMin
    unfold DescentHostDegree.gap DescentHostDegree.logDegree
    by_contra! zero
    have bad : Nat.clog 2 (2*T.Δ)=0 := by omega
    rw [bad,pow_zero] at pow
    omega
  calc
    _ = Scan.leafDepth (Scan.build raw (multiplierLoad wt f μ.val) D cap T.k) (e v) x := by
      change Scan.leafDepth (Scan.build (DynamicSplit.incoming rs) (multiplierLoad (Padded.table wt) f μ.val)
        D cap T.k) (Padded.front h (e v)) x=_
      rw [padded]
      unfold Scan.leafDepth
      simp_rw [Scan.padded_lookup (Padded.front h) raw (Padded.neighbors h raw)
        (multiplierLoad wt f μ.val) _ (Padded.live_neighbors h raw) (Padded.live_weight h wt f μ.val)]
    _ = Scan.leafDepth (Scan.build inc mass D cap T.k) v x := by
      rw [move,←reindex]
      unfold Scan.leafDepth
      simp_rw [Scan.lookup_reindex e inc mass D cap]
    _ = _ := Scan.leafDepth_eq inc (fun v w=>w∈T.near v) listed mass posD a (unit*T.cap) fit v x

include members in
/-- For each actual old site, its occupied name is precisely what the native winning row reads. -/
theorem physical_cell_at (x : W.graph.Site) :
    let v := (e (T.pos x)).castLE h
    let b := blk x
    let z := Scan.leafDepth rows v b
    (T.cellEmbedding e h μ (home x)).val=v.val*2^(T.k+1)+(2^z-1+group z b) := by
  dsimp only
  rw [embedding_value,show whereAt (home x)=colonyCode W.graph (unit*T.cap) T.near D a mass fit T.pos blk x from
    occupiedAddress_colonyOf ..,scanned_depth T e h μ rs members]
  rfl

end
end Hierarchy.DescentSixParty.StageInput

end OAI
