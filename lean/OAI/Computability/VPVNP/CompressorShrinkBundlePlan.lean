import OAI.Computability.VPVNP.CompressorGreedyLevelPlan
import OAI.Computability.VPVNP.CompressorRecordsShrinkInput
import OAI.Computability.VPVNP.CompressorShrinkTermRecipe
import OAI.Computability.VPVNP.CompressorShrinkMotifAbsolute
import OAI.Computability.VPVNP.CompressorBundleSortedWidths
import OAI.Computability.VPVNP.CompressorSlicePreparation

/-!
# Dense shrinking visits between greedy preparation and term selection

The preliminary placement uses layout zero. Classification, append, gather
and rank work in the dyadic rank arena. After ranking, its gathered-key
rectangle becomes the absolute motif ID rectangle. Sorted widths, the two
prefixes and AB pieces occupy the consecutive width arena. The resulting
heads are the inputs to the motif demand and term planners.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData PhaseRecipe BlockPlanner
open scoped Fin.CommRing

variable (step a : ℕ) (origin : Expr)

/-- Number of thick fields per bundle, one quarter of the product of the color-word count and
the input degree. -/
abbrev thickCount := 2^(Shrink.colors a) * 2^a / 4
/-- Per-bucket capacity used throughout the shrinking rank and width rectangles at this degree
exponent. -/
abbrev cap := ShrinkRankSpace.cap a

/-- Compute the number of directed bundles from the base vertices, tag count, residual lanes
and input degree. -/
def bundles := ((LevelFields.vertices step).mul ((Expr.lit (2^(Shrink.J a))).mul
  (LevelFields.residualLanes step))).mul (LevelFields.degree step)

/-- Address where preliminary placement begins, immediately after the greedy allocation. -/
def preliminary := GreedyLevelPlan.greedyStop step a origin
/-- Base address of one of the four preliminary placement columns, each reserving one word per
old site. -/
def placementColumn (j : Fin 4) := (preliminary step a origin).add
  ((Expr.lit j.val).mul (LevelFields.sites step))
/-- Start of the old-port owner column following the four preliminary site columns. -/
def owner := (preliminary step a origin).add ((Expr.lit 4).mul (LevelFields.sites step))
/-- Start of the classifier-key column following the owner word for every old port. -/
def key := (owner step a origin).add (LevelFields.slots step)
/-- First address of the per-bucket counts, following the old-port owner and key columns. -/
def counts := (owner step a origin).add ((Expr.lit 2).mul (LevelFields.slots step))
/-- Number of rank buckets, with one thick and one motif bucket for every directed bundle. -/
def bucketCount := (Expr.lit 2).mul (bundles step a)
/-- First address of the rectangle holding the appended old-port identifiers for the rank
buckets. -/
def ids := (counts step a origin).add (bucketCount step a)
/-- Total words in a rank rectangle, multiplying the number of thick and motif buckets by their
common capacity. -/
def rectangle := (bucketCount step a).mul (.lit (cap a))
/-- Start of the gathered-key rectangle, reused for absolute identifiers once the ranks have
been computed. -/
def gathered := (ids step a origin).add (rectangle step a)
/-- Start of the per-old-port rank column immediately following the gathered-key rectangle. -/
def ranks := (gathered step a origin).add (rectangle step a)
/-- First address of the sorted thick and motif width rectangles, after the rank column. -/
def sorted := (ranks step a origin).add (LevelFields.slots step)
/-- Words in one bundle-by-rank rectangle, for either the thick or the motif entries. -/
def blockSize := (bundles step a).mul (.lit (cap a))
/-- The expression for the CD absolute-ID rectangle head, one bundle-by-rank rectangle past the
gathered-key base. -/
def absoluteCD := (gathered step a origin).add (blockSize step a)
/-- First address of the thick and motif prefix-offset rectangles, following both sorted-width
rectangles. -/
def prefixStart := (sorted step a origin).add ((Expr.lit 2).mul (blockSize step a))
/-- First address of the per-bundle totals for the thick and motif prefix scans. -/
def totalStart := (prefixStart step a origin).add ((Expr.lit 2).mul (blockSize step a))
/-- First address of the AB piece-width rectangle, following the per-bucket totals. -/
def abStart := (totalStart step a origin).add (bucketCount step a)

/-- Collect the level dimensions, sorted widths, capacity and AB piece head needed by the
shrinking demand and term recipes. -/
def termInputs : ShrinkTermRecipe.Inputs :=
  ⟨LevelFields.vertices step,LevelFields.degree step,LevelFields.lanes step,LevelFields.residualLanes step,
    sorted step a origin,.lit (cap a),abStart step a origin⟩

variable (shape : DescriptorSpace.Shape)

/-- The original greedy labels, full base displacements and a fresh four-column
output. Only the preliminary use fixes the layout operand to zero. -/
def placementParams (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Fin 14 → Expr :=
  Fin.append (![LevelFields.residualLanes step,.lit (2^(Shrink.J a)),LevelFields.degree step,
    .lit (2^(Shrink.colors a)),.lit (Shrink.colors a - 1),.lit 0,
    origin,GreedyLevelPlan.offsetBase step a origin,LevelFields.incidence shape step 0,
    LevelFields.incidence shape step 2] : Fin 10 → Expr) (placementColumn step a origin)

/-- The classifier's eleven public operands, including level dimensions, old incidence,
preliminary placement columns and the owner and key destinations. -/
def classifyParams (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Fin 11 → Expr :=
  ![LevelFields.degree step,LevelFields.residualLanes step,.lit (2^(Shrink.J a)),.lit (2^(Shrink.colors a)),
    bundles step a,LevelFields.incidence shape step 3,placementColumn step a origin 1,placementColumn step a origin 0,
    placementColumn step a origin 2,owner step a origin,key step a origin]

/-- Public operands for appending the old slots to their owner buckets, including counts,
capacity and the ID rectangle. -/
def collectParams : Fin 6 → Expr :=
  ![LevelFields.slots step,owner step a origin,bucketCount step a,counts step a origin,.lit (cap a),ids step a origin]

/-- Public operands for gathering the classified keys by bundle and rank, including the
thick-entry count and both rectangle heads. -/
def gatherParams : Fin 7 → Expr :=
  ![.lit (thickCount a + cap a),.lit (thickCount a),bundles step a,.lit (cap a),
    ids step a origin,key step a origin,gathered step a origin]

/-- Public operands for finding each old port's rank from its owner, key, bucket count and the
gathered-key rectangle. -/
def rankParams : Fin 6 → Expr :=
  ![owner step a origin,key step a origin,gathered step a origin,.lit (cap a),counts step a origin,ranks step a origin]

/-- Public operands for scattering old incidence widths into the sorted rectangle at each
port's owner and rank. -/
def widthParams (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : Fin 5 → Expr :=
  ![owner step a origin,ranks step a origin,LevelFields.incidence shape step 5,.lit (cap a),sorted step a origin]

/-- Public operands for replacing gathered keys by absolute identifiers, using owner, rank,
key, degree and residual-lane data. -/
def absoluteParams : Fin 7 → Expr :=
  ![owner step a origin,ranks step a origin,key step a origin,.lit (cap a),gathered step a origin,
    LevelFields.degree step,LevelFields.residualLanes step]

/-- Select the width, start-offset and total columns for either the thick or the motif prefix
scan, together with its field count and row stride. -/
def prefixParams (motif : Bool) : Fin 5 → Expr :=
  let widths := sorted step a origin
  let starts := prefixStart step a origin
  let totals := totalStart step a origin
  let advance (x : Expr) := if motif then x.add (blockSize step a) else x
  ![.lit (if motif then cap a else thickCount a),.lit (cap a),advance widths,advance starts,
    if motif then totals.add (bundles step a) else totals]

/-- The AB piece worker's capacity, row stride, input total column and output heads for piece
widths and starts. -/
def abParams : Fin 5 → Expr :=
  ![.lit (cap a),.lit (cap a),totalStart step a origin,abStart step a origin,(abStart step a origin).add (blockSize step a)]

/-- Eleven chronological scans, each with its exact fixed instruction table,
return register, cursor bound and operand arity. -/
def visits (shape : DescriptorSpace.Shape) (step a : ℕ) (origin : Expr) : List Visit :=
  let fromZero {r k : ℕ} (code : List (PrimedStackRAM.Op r k)) (out : Fin r) (stop : Expr) (p : Fin k → Expr) :=
    ops code out (.lit 0) stop p
  let A := LevelFields.slots step
  [fromZero ShrinkRAM.visit 0 (LevelFields.sites step) (placementParams shape step a origin),
   fromZero SliceRAM.clearOps 0 (bucketCount step a) (fun _ ↦ counts step a origin),
   fromZero BundleRAM.visit 0 A (classifyParams shape step a origin),
   fromZero collectPreimage 3 A (collectParams step a origin),
   fromZero BundleGather.Fixed.visit 0 A (gatherParams step a origin),
   fromZero (PortRankRAM.visit (cap a)) 0 A (rankParams step a origin),
   fromZero BundleWidthScatter.visit 0 A (widthParams shape step a origin),
   fromZero BundlePrefixRAM.visit 0 ((bundles step a).mul (.lit (thickCount a))) (prefixParams step a origin false),
   fromZero BundlePrefixRAM.visit 0 (blockSize step a) (prefixParams step a origin true),
   fromZero ABWidths.visit 0 (blockSize step a) (abParams step a origin),
   fromZero MotifAbsolute.visit 0 A (absoluteParams step a origin)]

theorem visits_length : (visits shape step a origin).length = 11 := rfl

theorem operand_counts : (visits shape step a origin).map (fun v ↦ v.worker.params) =
    [14,1,11,6,7,6,5,5,5,5,7] := rfl


section Readback

variable {step a shape origin} {g w : ℕ} (X : State a (packingLaneBits a g))
variable {pub : Fin 5 → Word w} {state : Word w} {m : Memory w} {T : IncidenceDirectory w} {start : ℕ}

local notation "ev" => Expr.eval pub state m
local notation "N" => Fintype.card X.Base
local notation "S" => (Fintype.card X.Base * 2^(packingLaneBits a g) : ℕ)
local notation "Z" => ShrinkInput.plan X start
local notation "q" => ShrinkRankSpace.Shape.collectBank (ShrinkInput.plan X start) w
local notation "sh" => ShrinkInput.placementBank X T start
local notation "rankWord" => (Fin.ofNat (2^w) (ShrinkRankSpace.Shape.ranks (ShrinkInput.plan X start)))
local notation "W" => ShrinkInput.widthBase X start
local notation "scatter" => ShrinkWidthArena.scatterBank T q rankWord W
local notation "prefix" => ShrinkWidthArena.prefixBase X q W

/-- Each expression in the setup uses the input level's published scalars and
the greedy arena already installed at the supplied origin. -/
structure Reads (X : State a (packingLaneBits a g)) (shape : DescriptorSpace.Shape) (step : ℕ)
    (origin : Expr) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (start : ℕ) (T : IncidenceDirectory w) : Prop extends
    GreedyLevelPlan.Reads shape step a origin pub state m (Fintype.card X.Base) g start T where
  lanes : (LevelFields.lanes step).eval pub state m = ((2^(packingLaneBits a g) : ℕ) : Word w)

variable (h : Reads X shape step origin pub state m start T)

include h in
private theorem eval_sites : ev (LevelFields.sites step) = (S : Word w) := by
  change ev (LevelFields.vertices step)*ev (LevelFields.lanes step) = _
  rw [h.vertices,h.lanes,Nat.cast_mul]

include h in
private theorem eval_slots : ev (LevelFields.slots step) = ((Z).A : Word w) := by
  change ev (LevelFields.sites step)*ev (LevelFields.degree step) = ((S*2^a : ℕ) : Word w)
  simp only [eval_sites X h,h.degree,Nat.cast_mul]

include h in
private theorem eval_bundles : ev (bundles step a) = ((Z).B : Word w) := by
  change (ev (LevelFields.vertices step)*(((2^(Shrink.J a) : ℕ) : Word w)*ev (LevelFields.residualLanes step)))*ev (LevelFields.degree step) = _
  rw [h.vertices,h.residual,h.degree,← Nat.cast_mul,← Nat.cast_mul,← Nat.cast_mul]; rfl

private theorem eval_add (x y : Expr) : ev (x.add y) = ev x + ev y := rfl
private theorem eval_mul (x y : Expr) : ev (x.mul y) = ev x * ev y := rfl
private theorem eval_lit (k : ℕ) : ev (.lit k) = (k : Word w) := rfl

/-- Evaluation of the bundle-plan expressions yields the physical placement columns, rank-arena
addresses and capacities for this input graph. -/
structure HeadValues (X : State a (packingLaneBits a g)) (step : ℕ) (origin : Expr)
    (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) (start : ℕ) : Prop where
  placement (j : Fin 4) : Expr.eval pub state m (placementColumn step a origin j) = ((ShrinkInput.placementBase X start+j.val*(Fintype.card X.Base*2^(packingLaneBits a g)) : ℕ) : Word w)
  owner : Expr.eval pub state m (owner step a origin) = ((ShrinkInput.plan X start).owner : Word w)
  key : Expr.eval pub state m (key step a origin) = ((ShrinkInput.plan X start).key : Word w)
  counts : Expr.eval pub state m (counts step a origin) = ((ShrinkInput.plan X start).counts : Word w)
  bucketCount : Expr.eval pub state m (bucketCount step a) = ((2*(ShrinkInput.plan X start).B : ℕ) : Word w)
  ids : Expr.eval pub state m (ids step a origin) = ((ShrinkInput.plan X start).ids : Word w)
  rectangle : Expr.eval pub state m (rectangle step a) = ((ShrinkInput.plan X start).rectangleSize : Word w)
  gathered : Expr.eval pub state m (gathered step a origin) = ((ShrinkInput.plan X start).gathered : Word w)
  ranks : Expr.eval pub state m (ranks step a origin) = ((ShrinkInput.plan X start).ranks : Word w)
  sorted : Expr.eval pub state m (sorted step a origin) = (ShrinkInput.widthBase X start : Word w)
  blockSize : Expr.eval pub state m (blockSize step a) = (((ShrinkInput.plan X start).B*(ShrinkInput.plan X start).Q : ℕ) : Word w)
  absoluteCD : Expr.eval pub state m (absoluteCD step a origin) = (((ShrinkInput.plan X start).gathered + (ShrinkInput.plan X start).B*(ShrinkInput.plan X start).Q : ℕ) : Word w)

include h in
theorem head_values : HeadValues X step origin pub state m start := by
  have pre : ev (preliminary step a origin) = (ShrinkInput.placementBase X start : Word w) :=
    GreedyLevelPlan.eval_greedyStop h.toReads
  have ho : ev (owner step a origin) = ((Z).owner : Word w) := by
    rw [owner,eval_add,eval_mul,eval_lit,pre,eval_sites X h,← Nat.cast_mul,← Nat.cast_add]; rfl
  have hk : ev (key step a origin) = ((Z).key : Word w) := by
    rw [key,eval_add,ho,eval_slots X h,← Nat.cast_add]; rfl
  have hc : ev (counts step a origin) = ((Z).counts : Word w) := by
    rw [counts,eval_add,ho,eval_mul,eval_lit,eval_slots X h,← Nat.cast_mul,← Nat.cast_add]; rfl
  have hb : ev (bucketCount step a) = ((2*(Z).B : ℕ) : Word w) := by
    rw [bucketCount,eval_mul,eval_lit,eval_bundles X h,Nat.cast_mul]
  have hi : ev (ids step a origin) = ((Z).ids : Word w) := by rw [ids,eval_add,hc,hb,← Nat.cast_add]; rfl
  have rect : ev (rectangle step a) = ((Z).rectangleSize : Word w) := by
    rw [rectangle,eval_mul,hb,eval_lit,← Nat.cast_mul]
  have hg : ev (gathered step a origin) = ((Z).gathered : Word w) := by
    rw [gathered,eval_add,hi,rect,← Nat.cast_add]; rfl
  have hr : ev (ranks step a origin) = ((Z).ranks : Word w) := by
    rw [ranks,eval_add,hg,rect,← Nat.cast_add]; rfl
  have hs : ev (sorted step a origin) = (W : Word w) := by
    rw [sorted,eval_add,hr,eval_slots X h,← Nat.cast_add]; rfl
  have block : ev (blockSize step a) = (((Z).B*(Z).Q : ℕ) : Word w) := by
    rw [blockSize,eval_mul,eval_bundles X h,eval_lit,← Nat.cast_mul]
  refine ⟨?_,ho,hk,hc,hb,hi,rect,hg,hr,hs,block,?_⟩
  · intro j
    simp only [placementColumn,eval_add,pre,eval_mul,eval_lit,eval_sites X h,Nat.cast_add,Nat.cast_mul]
  · rw [absoluteCD,eval_add,hg,block,Nat.cast_add]

include h in
theorem placement_bank : (fun i ↦ ev (placementParams shape step a origin i)) = sh := by
  have heads := head_values X h
  have off := GreedyLevelPlan.eval_offsetBase h.toReads
  funext i
  fin_cases i
  · exact h.residual
  · rfl
  · exact h.degree
  · rfl
  · rfl
  · rfl
  · exact h.origin
  · exact off
  · exact h.incidence 0
  · exact h.incidence 2
  · exact heads.placement 0
  · exact heads.placement 1
  · exact heads.placement 2
  · exact heads.placement 3

include h in
theorem rank_banks (fit : (Z).stop < 2^w) :
    (fun i ↦ ev (classifyParams shape step a origin i)) = (Z).classifyBank T sh ∧
    (fun i ↦ ev (collectParams step a origin i)) = q ∧
    (fun i ↦ ev (gatherParams step a origin i)) = BundleGather.Fixed.parameters ((Z).gatheredTable w T) ∧
    (fun i ↦ ev (rankParams step a origin i)) =
      BundleGather.rankPublic q (Fin.ofNat _ (Z).key) (Fin.ofNat _ (Z).gathered) rankWord ∧
    (fun i ↦ ev (widthParams shape step a origin i)) = scatter := by
  have v := head_values X h
  have hz := (Z).values T sh Fintype.card_pos fit
  have stride : ev (.lit (cap a)) = Fin.ofNat (2^w) (q 4).val := by rw [hz.stride]; rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · funext i; fin_cases i
    · exact h.degree
    · exact h.residual
    · rfl
    · rfl
    · exact eval_bundles X h
    · exact h.incidence 3
    · exact v.placement 1
    · exact v.placement 0
    · exact v.placement 2
    · exact v.owner
    · exact v.key
  · funext i; fin_cases i
    · exact eval_slots X h
    · exact v.owner
    · exact v.bucketCount
    · exact v.counts
    · rfl
    · exact v.ids
  · funext i; fin_cases i
    · rfl
    · rfl
    · exact eval_bundles X h
    · exact stride
    · exact v.ids
    · exact v.key
    · exact v.gathered
  · funext i; fin_cases i
    · exact v.owner
    · exact v.key
    · exact v.gathered
    · rfl
    · exact v.counts
    · exact v.ranks
  · funext i; fin_cases i
    · exact v.owner
    · exact v.ranks
    · exact h.incidence 5
    · rfl
    · exact v.sorted

/-- The two scattered classes reuse the gathered keys after the rank scan. -/
def absoluteBank (z : ShrinkRankSpace.Shape) (w : ℕ) : Fin 7 → Word w :=
  ![z.owner,z.ranks,z.key,z.Q,z.gathered,(2^z.degreeBits : ℕ),(2^z.residualBits : ℕ)]

include h in
theorem absolute_bank : (fun i ↦ ev (absoluteParams step a origin i)) = absoluteBank Z w := by
  have v := head_values X h
  funext i; fin_cases i
  · exact v.owner
  · exact v.ranks
  · exact v.key
  · rfl
  · exact v.gathered
  · exact h.degree
  · exact h.residual

/-- The old gather rectangle ends at the rank column. The other two inputs
(owner and key) end before that rectangle. This establishes the scatter's
frame without allocating another pair of rectangles. -/
theorem absolute_layout (fit : (Z).stop < 2^w) :
    BundleWidthScatter.Layout (MotifAbsolute.columns (absoluteBank Z w)) (Z).A
      (N*(2^(Shrink.J a)*2^g)) (2^a) (Shrink.colors a) := by
  have scalar := (Z).scalarFits Fintype.card_pos fit
  have stride : (MotifAbsolute.columns (absoluteBank Z w) 3).val = (Z).Q := Nat.mod_eq_of_lt scalar.2.2.1
  have bound : (Z).ranks+(Z).A < 2^w := fit
  have rect : (Z).gathered+((Z).B+(Z).B)*(Z).Q = (Z).ranks := by
    change (Z).gathered+((Z).B+(Z).B)*(Z).Q = (Z).gathered+(2*(Z).B)*(Z).Q
    rw [two_mul]
  have ho : (Z).owner+(Z).A ≤ (Z).gathered := by
    simp only [ShrinkRankSpace.Shape.owner,ShrinkRankSpace.Shape.gathered,ShrinkRankSpace.Shape.ids,
      ShrinkRankSpace.Shape.counts]
    omega
  have hk : (Z).key+(Z).A ≤ (Z).gathered := by
    simp only [ShrinkRankSpace.Shape.key,ShrinkRankSpace.Shape.gathered,ShrinkRankSpace.Shape.ids,
      ShrinkRankSpace.Shape.counts]
    omega
  have buckets := scalar.2.1
  have out : (MotifAbsolute.columns (absoluteBank Z w) 4).val = (Z).gathered := Nat.mod_eq_of_lt (by omega)
  have ownVal : (Fin.ofNat (2^w) (Z).owner).val = (Z).owner := Nat.mod_eq_of_lt (by omega)
  have keyVal : (Fin.ofNat (2^w) (Z).key).val = (Z).key := Nat.mod_eq_of_lt (by omega)
  have rankVal : (Fin.ofNat (2^w) (Z).ranks).val = (Z).ranks := Nat.mod_eq_of_lt (by omega)
  refine ⟨stride.ge,?_,?_,?_,?_⟩
  · change (Z).B+(Z).B ≤ 2^w; omega
  · intro i; fin_cases i
    · change (Fin.ofNat (2^w) (Z).owner).val+(Z).A ≤ _; rw [ownVal]; omega
    · change (Fin.ofNat (2^w) (Z).ranks).val+(Z).A ≤ _; rw [rankVal]; omega
    · change (Fin.ofNat (2^w) (Z).key).val+(Z).A ≤ _; rw [keyVal]; omega
  · rw [stride,out]; change (Z).gathered+((Z).B+(Z).B)*(Z).Q ≤ _; omega
  · intro i; rw [stride,out]; fin_cases i
    · left; change (Fin.ofNat (2^w) (Z).owner).val+_ ≤ _; rwa [ownVal]
    · right
      change (Z).gathered+((Z).B+(Z).B)*(Z).Q ≤ (Fin.ofNat (2^w) (Z).ranks).val
      rw [rankVal,rect]
    · left; change (Fin.ofNat (2^w) (Z).key).val+_ ≤ _; rwa [keyVal]

include h in
private theorem end_heads (fit : (Z).stop < 2^w) :
    ev (prefixStart step a origin) = (prefix : Word w) ∧
    ev (totalStart step a origin) = ((prefix+2*((Z).B*(Z).Q) : ℕ) : Word w) ∧
    ev (abStart step a origin) = (ShrinkWidthArena.abBase X q W : Word w) := by
  have v := head_values X h
  have stride := ((Z).values T sh Fintype.card_pos fit).stride
  have p : ev (prefixStart step a origin) = (prefix : Word w) := by
    rw [prefixStart,eval_add,v.sorted,eval_mul,eval_lit,v.blockSize,← Nat.cast_mul,← Nat.cast_add,
      ShrinkWidthArena.prefixBase,stride]
  have t : ev (totalStart step a origin) = ((prefix+2*((Z).B*(Z).Q) : ℕ) : Word w) := by
    rw [totalStart,eval_add,p,eval_mul,eval_lit,v.blockSize,← Nat.cast_mul,← Nat.cast_add]
  refine ⟨p,t,?_⟩
  rw [abStart,eval_add,t,v.bucketCount,← Nat.cast_add,ShrinkWidthArena.abBase,stride]

include h in
theorem prefix_bank (motif : Bool) (fit : (Z).stop < 2^w) :
    (fun i ↦ ev (prefixParams step a origin motif i)) = ShrinkWidthArena.prefixBank X T q rankWord W motif := by
  have v := head_values X h
  obtain ⟨hp,ht,_⟩ := end_heads X h fit
  have stride : (scatter 3).val = (Z).Q := ((Z).values T sh Fintype.card_pos fit).stride
  have width : (scatter 4).val = W := Nat.mod_eq_of_lt fit
  cases motif <;> funext i <;> fin_cases i
  · rfl
  · rfl
  · change ev (sorted step a origin) = Fin.ofNat _ (scatter 4).val
    rw [width]; exact v.sorted
  · exact hp
  · change ev (totalStart step a origin) = Fin.ofNat _ (prefix+2*((Z).B*(scatter 3).val))
    rw [stride]; exact ht
  · rfl
  · rfl
  · change ev ((sorted step a origin).add (blockSize step a)) = Fin.ofNat _ ((scatter 4).val+(Z).B*(scatter 3).val)
    rw [eval_add,v.sorted,v.blockSize,width,stride,← Nat.cast_add]; rfl
  · change ev ((prefixStart step a origin).add (blockSize step a)) = Fin.ofNat _ (prefix+(Z).B*(scatter 3).val)
    rw [eval_add,hp,v.blockSize,stride,← Nat.cast_add]; rfl
  · change ev ((totalStart step a origin).add (bundles step a)) =
      Fin.ofNat _ (prefix+2*((Z).B*(scatter 3).val)+(Z).B)
    rw [eval_add,ht,eval_bundles X h,stride,← Nat.cast_add]; rfl

include h in
theorem ab_bank (fit : (Z).stop < 2^w) :
    (fun i ↦ ev (abParams step a origin i)) = ShrinkWidthArena.abBank X T q rankWord W := by
  have ab := (end_heads X h fit).2.2
  have total := congrFun (prefix_bank X h false fit) 4
  have v := head_values X h
  funext i; fin_cases i
  · rfl
  · rfl
  · exact total
  · exact ab
  · change ev ((abStart step a origin).add (blockSize step a)) = _
    rw [eval_add,ab,v.blockSize,← Nat.cast_add]; rfl

include h in
theorem term_input (fit : (Z).stop < 2^w) :
    ShrinkTermRecipe.Describes (termInputs step a origin) X pub state m scatter (ShrinkWidthArena.abBase X q W) :=
  ⟨h.vertices,h.degree,h.lanes,h.residual,(head_values X h).sorted,rfl,(end_heads X h fit).2.2⟩

include h in
/-- Cursor bounds in native order. The first position scan includes every old
site. Each subsequent classification or scatter visits the old arcs, while
the two prefix scans visit the populated parts of the thick and CD rows. -/
theorem stop_counts :
    (visits shape step a origin).map (fun v ↦ ev v.stop) =
      List.map (fun j : ℕ ↦ (j : Word w)) [S,2*(Z).B,(Z).A,(Z).A,(Z).A,(Z).A,(Z).A,
        (Z).B*thickCount a,(Z).B*(Z).Q,(Z).B*(Z).Q,(Z).A] := by
  have v := head_values X h
  simp only [visits,List.map_cons,List.map_nil,ops,eval_sites X h,eval_slots X h,v.bucketCount,v.blockSize,
    eval_mul,eval_lit,eval_bundles X h,← Nat.cast_mul]

end Readback

end CompressorRecords.ShrinkBundlePlan

end VPVNP
end Computability
end OAI
