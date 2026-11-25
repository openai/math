import OAI.Hierarchy.DescentOriginalSeedArchive
import OAI.Hierarchy.DescentOriginalSeedLink
import OAI.Hierarchy.DescentSeedPanelReceipt
import OAI.Hierarchy.DescentNormalizationNames
import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentOrdinaryVenueRows
import OAI.Hierarchy.DescentSourceSorted
import OAI.Hierarchy.DescentHiddenReset
import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentEpochOrderTypes
import OAI.Hierarchy.DescentPackedMatchSourceChart
import OAI.Hierarchy.DescentSeedNodeOrder
import OAI.Hierarchy.DescentResetNodeChronology

namespace OAI
/-! # One chronological branch of issued native tables

Ordinary steps use one scanned source, its chosen coefficient profile, its
normalization, and the physically published edge and pair ordinals. A reset
step stores the same closed reset that defines its next reached placement.
-/

namespace Hierarchy.DescentSixParty.Chronology

open DescentCompiler DescentKernelHistory DescentStageEdgeReceipt DescentInitialHost Catalyst
open DescentRotor DescentPacking DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε u : ℝ} {S : AtomSchedule} {k : ℕ}

/-- Source rows visit the dyadic heap first, then the host, then the group.
This order is fixed by the exact reached parent before sampling a child profile. -/
def inputNumbers {W : MarkedWorld F d P bits} {i z D wire hist : ℕ}
    (he : 0≤ε) (cap : Reached W G q ε S k i z D wire hist) : ScanNumbers he cap.placement.stage :=
  DescentPacking.PairRAM.globalNumberBy W.graph W.core (scanHomeAt he cap.placement.stage)
    (scanColorAt he cap.placement.stage) cap.placement.stage.cap
    ((DescentPacking.PackedMatch.Local.sourceChart he cap.placement
      (Function.Embedding.refl _) cap.vertex).trans Fin.valEmbedding)

/-- A genuine ordinary step out of the specified reached placement. The tape
orders the new graph and the chosen pair numbers address the same tape. -/
structure OrdinaryLink {W : MarkedWorld F d P bits} {i z D wire hist : ℕ}
    (source : Reached W G q ε S k i z D wire hist) (he : 0≤ε)
    (T : StageInput W G u ε) (p : (T.result he).Choice) (n : Normalize ((T.result he).state p))
    {z' D' : ℕ} (target : Reached n.result G q ε S k (i+1) z' D' wire hist) where
  sourceRate : u=q*source.placement.wire
  placement : HEq T source.placement.stage
  quantum : T.z=source.placement.z
  sourceCounts : ∀v,(T.records v).length=(source.placement.records v).length
  sourcePosition : ∀v,HEq (T.pos v) (source.placement.pos v)
  sourceFlags : T.hub=(fun v=>source.placement.hub (source.placement.pos v).2)
  grainStep : z=z'*G.b
  tape : Tape n.result.graph.Edge
  pair : ScanNumbers he T
  inputPair : ScanNumbers he T
  inputRows : HEq inputPair (inputNumbers he source)
  issued : IssuedRows he T p source.order
    (groupRank (Fin.valEmbedding (n := S.groupCount i)) (source.vertex.trans Fin.valEmbedding))
    _ n tape pair
  particles : ParticleRows he T p _ n (fun v=>(target.placement.records v).length)
    (fun v=>target.placement.hub (target.placement.pos v).2)
  edges : target.order=tape.selector
  cuts : Normalize.CutsEqual source.placement.z n
  capacity : target.placement.cap=2^(DescentHostDegree.gainExponent 20 D)*G.b*source.placement.cap
  hubRows : ∃ (age : i<S.length) (radix : S.radix=2^k) (chart : target.V↪DescentHostDirectory.Key source.V),
    GroupStage.HubRows source.placement he (S.groupDigits age radix) target.placement chart
  hostOrdinal : ∃ (age : i<S.length) (radix : S.radix=2^k) (chart : target.V↪DescentHostDirectory.Key source.V),
    GroupStage.HubRows source.placement he (S.groupDigits age radix) target.placement chart ∧
    (∀v, (target.vertex v).val =
      let key:=chart v
      let slots:=2^DescentHostDegree.packExponent 20 source.placement.degree+2
      ((source.vertex key.1).val * (2^(k+1)-1) +
        DescentHostDirectory.nodeNumber key.2.1.1 key.2.1.2)*slots+key.2.2) ∧
    (∀v,chart v∈DescentHostDirectory.keys k (2^DescentHostDegree.packExponent 20 source.placement.degree+2)) ∧
    ∀v,target.placement.hub v=DescentHostDirectory.publishedHub source.placement.hub k
      (DescentHostDegree.gainExponent 20 source.placement.degree) (chart v)

  venueRows : ∃ (age : i<S.length) (radix : S.radix=2^k) (chart : target.V↪DescentHostDirectory.Key source.V),
    GroupStage.VenueRows source.placement he T p (S.groupDigits age radix) n target.placement chart ∧
    ∀v,(target.vertex v).val=
      let key:=chart v
      let slots:=2^DescentHostDegree.packExponent 20 source.placement.degree+2
      ((source.vertex key.1).val*(2^(k+1)-1)+DescentHostDirectory.nodeNumber key.2.1.1 key.2.1.2)*slots+key.2.2
  sourceSorted : SourceSorted n.result target.order
  hostCount : Fintype.card target.V=Fintype.card source.V*(2^(k+1)-1)*
    (2^DescentHostDegree.packExponent 20 source.placement.degree+2)

  degreeSlot : ∃j<S.rounds,D=atRound j
  nameCount : n.nameCount=1
  adjacency :
    let δ:=source.placement.degree
    let slots:=2^DescentHostDegree.packExponent 20 δ+2
    ∃chart : target.V≃DescentHostDirectory.Host source.V k slots,
      (∀v,let key:=(chart v).val
          (target.vertex v).val=((source.vertex key.1).val*(2^(k+1)-1)+
            DescentHostDirectory.nodeNumber key.2.1.1 key.2.1.2)*slots+key.2.2) ∧
      ∀u v,v∈target.placement.near u ↔ chart v∈DescentHostDirectory.restrictedNear source.placement.near
        (DescentHostDegree.gap δ+DescentHostDegree.gainExponent 20 δ) k slots (chart u)
  nextDegree : D'=ordinaryDegree D

/-- This type is indexed by the actual reached object, including its
order. The ordinary constructor has a named predecessor and choice; the
reset constructor has exactly the successor of that particular closed reset. -/
inductive Path {W₀ : MarkedWorld F d P bits} {j z₀ D₀ wire hist : ℕ}
    (start : Reached W₀ G q ε S k j z₀ D₀ wire hist) :
    {W : MarkedWorld F d P bits}→{i z D : ℕ}→Reached W G q ε S k i z D wire hist→Type 2 where
  | here : Path start start
  | ordinary {W : MarkedWorld F d P bits} {i z D z' D' : ℕ}
      {source : Reached W G q ε S k i z D wire hist} (prev : Path start source)
      {u : ℝ} {he : 0≤ε} {T : StageInput W G u ε} {p : (T.result he).Choice}
      {n : Normalize ((T.result he).state p)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
      (ticket : OrdinaryLink source he T p n target) : Path start target
  | reset {W : MarkedWorld F d P bits} {i z D n h C f g cut tail : ℕ}
      {source : Reached W G q ε S k i z D wire hist} (prev : Path start source)
      {ctl : ResetRates G S k D n h C f g cut tail} (closed : ClosedReset source ctl) :
      Path start closed.next

def OrdinaryLink.advance {W : MarkedWorld F d P bits} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T p n target) (a : Archive W) : Archive n.result :=
  ⟨_,_,ticket.issued.nodeOrder a.bit a.order,
    DescentHistoryOrder.ordinaryRank he T a.bit p n a.hiddenOrder source.order ticket.pair⟩

variable {W : MarkedWorld F d P bits} {i z D n h C f g cut tail wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}

open LinearAlgebra.SpectralBooks ThreeFlat Expander NonlinearExpanders in
private theorem transportMenu {n₁ n₂ h C w₁ w₂ : ℕ} (back : Graph n₁ h) (front : Graph n₂ h)
    (dim : n₁=n₂) (same : HEq back front) (width : w₁=w₂)
    (menu : ∀π,Configures F front.arcs C w₂ π) : ∀π,Configures F back.arcs C w₁ π := by
  subst n₂
  rw [eq_of_heq same,width]
  exact menu

theorem resetMenu (b : ClosedReset cap ctl) : ∀π,Configures F b.reset.graph.arcs C b.reset.width π :=
  transportMenu b.reset.graph ctl.board b.dimension b.graph b.width ctl.menu

/-- Transport the archive through the real incoming grain subdivision, the
lane-batched native bank and the final site/edge permutations of this reset. -/
def resetArchive (b : ClosedReset cap ctl) (p : ℕ) (hp : 0<p) (whole : p∣b.reset.unit)
    (a : Archive W) : Archive b.reblock.result := by
  let split := BitDescription.granular W b.count (z*G.b) b.fit a.bit
  let key := DescentOrderedReset.grains W b.count b.order
  let vertex := b.frame.host.symm.toEmbedding.trans cap.vertex
  have fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
  let r := split.batchedReset b.reset b.terminals key _ p hp fit (resetMenu b)
  let order := NodeOrder.fromBankOrdinal split b.reset b.terminals key _ p hp fit (resetMenu b)
    vertex a.order (DescentOrderedWords.address b.order b.count)
  let hidden := DescentHistoryOrder.resetHidden split b.reset b.terminals key _ p hp fit (resetMenu b) a.hiddenOrder
  let cable := b.reset.resetTag b.terminals (vertex.trans Fin.valEmbedding) (key.trans Fin.valEmbedding)
  exact ⟨BitDescription.follow b.reblock r,_,(NodeOrder.followNames b.reblock r).trans order,
    DescentHistoryOrder.followed b.reblock r hidden cable⟩

/-- The only arithmetic precondition of the archive fold is that each
actually installed reset bank uses a whole number of lanes. -/
def Path.whole {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ w t : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ w t} {last : Reached W₁ G q ε S k i₁ z₁ D₁ w t}
    (p : ℕ) (path : Path start last) : Prop := by
  induction path with
  | here => exact True
  | ordinary prev ticket ih => exact ih
  | reset prev b ih => exact ih ∧ p ∣ b.reset.unit

def Path.archive {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ w t : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ w t} {last : Reached W₁ G q ε S k i₁ z₁ D₁ w t}
    (p : ℕ) (hp : 0<p) (a : Archive W₀) (path : Path start last) (whole : path.whole p) : Archive W₁ := by
  revert whole
  induction path with
  | here => exact fun _ => a
  | ordinary prev ticket ih => exact fun ok => ticket.advance (ih ok)
  | reset prev b ih => exact fun ok => resetArchive b p hp ok.2 (ih ok.1)

/-- The public identity of one ordinary transition includes its actual input
world, measured scan, selected profile, and post-selection normalization. -/
structure Selection (F P : Type) [Field F] (d : ℕ) (bits : P→ℕ) (G : PoweredGadget F) (ε : ℝ) where
  world : MarkedWorld F d P bits
  rate : ℝ
  nonneg : 0≤ε
  stage : StageInput world G rate ε
  choice : (stage.result nonneg).Choice
  reblock : Normalize ((stage.result nonneg).state choice)

def OrdinaryLink.selection {W : MarkedWorld F d P bits} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (_ : OrdinaryLink source he T p n target) : Selection F P d bits G ε := ⟨W,u,he,T,p,n⟩

section Compose
variable {W₀ W₁ W₂ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ w t : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ w t} {middle : Reached W₁ G q ε S k i₁ z₁ D₁ w t}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ w t}

def Path.append (x : Path first middle) (y : Path middle last) : Path first last := by
  induction y with
  | here => exact x
  | ordinary prev ticket ih => exact .ordinary ih ticket
  | reset prev b ih => exact .reset ih b

/-- The capacity multiplier of a real stage is public once the common
degree of its ordinary round or the reset template has been fixed. -/
def OrdinaryLink.factor {W : MarkedWorld F d P bits} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (_ : OrdinaryLink source he T c n target) := 2^(DescentHostDegree.gainExponent 20 D)*G.b

def Path.capFactors (x : Path first middle) : List ℕ := by
  induction x with
  | here => exact []
  | ordinary prev ticket ih => exact ih ++ [ticket.factor]
  | reset prev b ih => exact ih ++ [b.factor]

theorem Path.capFactors_append (x : Path first middle) (y : Path middle last) :
    (x.append y).capFactors=x.capFactors++y.capFactors := by
  induction y with
  | here=>simp [append,capFactors]
  | ordinary prev ticket ih =>
    change (x.append prev).capFactors ++ [ticket.factor] =
      x.capFactors ++ (prev.capFactors ++ [ticket.factor])
    rw [ih,List.append_assoc]
  | reset prev closed ih =>
    change (x.append prev).capFactors ++ [closed.factor] =
      x.capFactors ++ (prev.capFactors ++ [closed.factor])
    rw [ih,List.append_assoc]

theorem Path.capacity_eq (x : Path first middle) :
    middle.placement.cap=x.capFactors.prod*first.placement.cap := by
  induction x with
  | here=>simp [capFactors]
  | ordinary prev ticket ih=>
    rw [ticket.capacity,ih];simp [capFactors,OrdinaryLink.factor,List.prod_append];ring
  | reset prev closed ih=>
    rw [closed.next_capacity,ih];simp [capFactors,ClosedReset.factor,List.prod_append];ring

theorem Path.capFactors_length (x : Path first middle) :
    i₀+x.capFactors.length=i₁ := by
  induction x with
  | here=>simp [capFactors]
  | ordinary prev ticket ih =>
    change i₀ + (prev.capFactors ++ [ticket.factor]).length = _ + 1
    simp only [List.length_append,List.length_singleton,← Nat.add_assoc]
    exact congrArg (· + 1) ih
  | reset prev closed ih =>
    change i₀ + (prev.capFactors ++ [closed.factor]).length = _ + 1
    simp only [List.length_append,List.length_singleton,← Nat.add_assoc]
    exact congrArg (· + 1) ih

/-- A fixed pre-mounted table can obtain the exact capacity of every
earlier reached world using only its public age and the original seed cap. -/
theorem Path.capacity_prefix (x : Path first middle) (y : Path middle last)
    (calendar : List ℕ) (paint : (x.append y).capFactors=calendar) :
    middle.placement.cap=(calendar.take (i₁-i₀)).prod*first.placement.cap := by
  rw [←paint,x.capFactors_append y,List.take_left' (by have:=x.capFactors_length;omega)]
  exact x.capacity_eq

theorem OrdinaryLink.degreeClass_factor {W : MarkedWorld F d P bits} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (link : OrdinaryLink source he T c n target) :
    degreeClass G.b link.factor=DescentHostDegree.logDegree source.placement.degree := by
  rw [source.branch]
  unfold degreeClass OrdinaryLink.factor
  rw [Nat.mul_div_cancel _ G.base_pos,Nat.log2_two_pow]
  unfold DescentHostDegree.gainExponent DescentHostDegree.packExponent
  omega

theorem OrdinaryLink.factor_at {W : MarkedWorld F d P bits} {age z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k age z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (link : OrdinaryLink source he T c n target)
    {X Y : MarkedWorld F d P bits} {start zz₀ dd₀ finish zz₁ dd₁ : ℕ}
    {first : Reached X G q ε S k start zz₀ dd₀ wire hist}
    {last : Reached Y G q ε S k finish zz₁ dd₁ wire hist}
    (before : Path first source) (later : Path target last) (calendar : List ℕ)
    (schedule : ((Path.ordinary before link).append later).capFactors=calendar) :
    (calendar.drop (age-start)).head?=some link.factor := by
  rw [←schedule,Path.capFactors_append]
  change (((before.capFactors++[link.factor])++later.capFactors).drop (age-start)).head?=_
  rw [List.append_assoc,List.drop_left' (by have:=before.capFactors_length;omega)]
  rfl

/-- Chronological stage records preserve the existentially chosen scan itself,
including its source, price and post-selection graph. -/
def Path.selections (x : Path first middle) : List (Selection F P d bits G ε) := by
  induction x with
  | here => exact []
  | ordinary prev ticket ih => exact ih ++ [ticket.selection]
  | reset prev b ih => exact ih

abbrev RankedSelection (F P : Type) [Field F] (d : ℕ) (bits : P→ℕ) (G : PoweredGadget F) (ε : ℝ) :=
  Σ e : Selection F P d bits G ε, ScanNumbers e.nonneg e.stage

def Path.ranked (x : Path first middle) : List (RankedSelection F P d bits G ε) := by
  induction x with
  | here => exact []
  | ordinary prev ticket ih => exact ih ++ [⟨ticket.selection,ticket.pair⟩]
  | reset prev b ih => exact ih

def Path.inputRanked (x : Path first middle) : List (RankedSelection F P d bits G ε) := by
  induction x with
  | here => exact []
  | ordinary prev ticket ih => exact ih ++ [⟨ticket.selection,ticket.inputPair⟩]
  | reset prev b ih => exact ih

theorem Path.inputRanked_append (x : Path first middle) (y : Path middle last) :
    (x.append y).inputRanked=x.inputRanked++y.inputRanked := by
  induction y with
  | here=>simp [Path.append,Path.inputRanked]
  | ordinary prev ticket ih =>
    change (x.append prev).inputRanked ++ [⟨ticket.selection,ticket.inputPair⟩] =
      x.inputRanked ++ (prev.inputRanked ++ [⟨ticket.selection,ticket.inputPair⟩])
    rw [ih,List.append_assoc]
  | reset prev b ih=>exact ih

theorem Path.ranked_append (x : Path first middle) (y : Path middle last) :
    (x.append y).ranked=x.ranked++y.ranked := by
  induction y with
  | here=>simp [Path.append,Path.ranked]
  | ordinary prev ticket ih =>
    change (x.append prev).ranked ++ [⟨ticket.selection,ticket.pair⟩] =
      x.ranked ++ (prev.ranked ++ [⟨ticket.selection,ticket.pair⟩])
    rw [ih,List.append_assoc]
  | reset prev b ih=>exact ih

def resetAligned {W : MarkedWorld F d P bits} {i z D n h C f g cut tail wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset cap ctl) (p R : ℕ) : Prop :=
  0<b.reset.unit ∧ p∣b.reset.unit ∧ max 1 (max b.reset.width (C*b.reset.width))≤R

def OrdinaryLink.aligned {W : MarkedWorld F d P bits} {i z D z' D' wire hist : ℕ}
    {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
    {T : StageInput W G u ε} {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (_ : OrdinaryLink source he T c n target) (p : ℕ) : Prop := p∣T.z

def Path.aligned (p R : ℕ) (x : Path first middle) : Prop := by
  induction x with
  | here => exact True
  | ordinary prev ticket ih => exact ih ∧ ticket.aligned p
  | reset prev b ih => exact ih ∧ resetAligned b p R

theorem Path.aligned_append (p R : ℕ) (x : Path first middle) (y : Path middle last)
    (hx : x.aligned p R) (hy : y.aligned p R) : (x.append y).aligned p R := by
  induction y with
  | here=>exact hx
  | ordinary prev ticket ih=>exact ⟨ih hy.1,hy.2⟩
  | reset prev b ih=>exact ⟨ih hy.1,hy.2⟩

theorem Path.aligned_whole {p R : ℕ} (x : Path first middle) (hx : x.aligned p R) : x.whole p := by
  induction x with
  | here=>trivial
  | ordinary prev ticket ih=>exact ih hx.1
  | reset prev b ih=>exact ⟨ih hx.1,hx.2.2.1⟩

def Path.ordinaryOnly (x : Path first middle) : Prop := by
  induction x with
  | here => exact True
  | ordinary prev ticket ih => exact ih
  | reset prev b ih => exact False

/-- A nonempty ordinary prefix ends in a physically named graph sorted by its genuine input source.
This applies after any reset and also when the initial seed has a different ordering. -/
theorem Path.ordinary_sorted (x : Path first middle) (only : x.ordinaryOnly) (elapsed : i₀ < i₁) :
    SourceSorted W₁ middle.order := by
  cases x with
  | here=>omega
  | ordinary prev step=>exact step.sourceSorted
  | reset prev receipt=>exact only.elim

theorem Path.ordinaryOnly_append (x : Path first middle) (y : Path middle last)
    (hx : x.ordinaryOnly) (hy : y.ordinaryOnly) : (x.append y).ordinaryOnly := by
  induction y with
  | here=>exact hx
  | ordinary prev ticket ih=>exact ih hy
  | reset prev b ih=>exact hy.elim

theorem Path.selections_append (x : Path first middle) (y : Path middle last) :
    (x.append y).selections=x.selections++y.selections := by
  induction y with
  | here=>simp [Path.append,Path.selections]
  | ordinary prev ticket ih =>
    change (x.append prev).selections ++ [ticket.selection] =
      x.selections ++ (prev.selections ++ [ticket.selection])
    rw [ih,List.append_assoc]
  | reset prev b ih=>exact ih

theorem Path.whole_append (p : ℕ) (x : Path first middle) (y : Path middle last)
    (left : x.whole p) (right : y.whole p) : (x.append y).whole p := by
  induction y with
  | here=>exact left
  | ordinary prev ticket ih=>exact ih right
  | reset prev b ih=>exact ⟨ih right.1,right.2⟩
end Compose

def sourceChoice (he : 0≤ε) {H : Histories F d P bits} {n : ℕ} (v : Schedule G (u:=u) he n H) (c : (Schedule.finish G he v).Choice) : H.Choice :=
  match n,H,v,c with
  | 0,_,_,c=>c
  | _+1,_,⟨_,rest⟩,c=>(sourceChoice he rest c).1

def scheduled (he : 0≤ε) {H : Histories F d P bits} {n : ℕ} (v : Schedule G (u:=u) he n H) (c : (Schedule.finish G he v).Choice) :
    List (Selection F P d bits G ε) :=
  match n,H,v,c with
  | 0,_,_,_=>[]
  | _+1,_,⟨a,rest⟩,c=>
    let branch:=sourceChoice he rest c
    ⟨_,_,he,a.placement branch.1,branch.2,a.reblock branch.1 branch.2⟩::scheduled he rest c

def rankedSchedule (he : 0≤ε) {H : Histories F d P bits} {n : ℕ} (v : Schedule G (u:=u) he n H)
    (order : DescentTerminalEpochDecoder.ScheduleOrders G he v) (c : (Schedule.finish G he v).Choice) :
    List (RankedSelection F P d bits G ε) :=
  match n,H,v,order,c with
  | 0,_,_,_,_=>[]
  | _+1,_,⟨a,rest⟩,order,c=>
    let branch:=sourceChoice he rest c
    ⟨⟨_,_,he,a.placement branch.1,branch.2,a.reblock branch.1 branch.2⟩,order.1 branch.1⟩::
      rankedSchedule he rest order.2 c

end
end Hierarchy.DescentSixParty.Chronology

end OAI
