import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.PhysicalTreeFee
import OAI.ThreeFlat.Diagonal.PhysicalProgramFreshPrices
import OAI.ThreeFlat.Diagonal.PhysicalSelectedWork
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology

namespace OAI
/-! # Admission of the actual typed forests into the scheduled root work allowance -/

set_option quotPrecheck false

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) (u rem : ℕ) {lanes : ℕ}
local notation "P" => B.repeat (u^8)
local notation "W" => 16*u^10
local notation "V" => 2^(u^10)
variable (A : State (2^B.exponent 0) lanes) (budget : lanes=(B.repeat (u^8)).charge+rem)
local notation "R" => (P).onLanes rem A budget
local notation "J" => (P).assembleOnLanes rem A budget (Pins:=Pins)

/-- The actual published node weights, transported to the raw trace lane count. -/
def chargeOnLanes : (R).Charges := by
  subst lanes
  exact B.charges (u^8) rem A

omit [Fintype F] in
/-- A real terminal node retains its fixed work unit even when it has no
surviving endpoints. -/
theorem rootPositiveOnLanes (h : (R).plan.History) (start : A.Site→ℕ)
    (floor : ∀ x,1+A.incidentWidth x≤ start x) (site : ((R).plan.finish h).Site) :
    1≤(R).chargeAt h (B.chargeOnLanes u rem A budget) start site := by
  subst lanes
  have root:=B.terminal_charge_covers (u^8) rem A h start (fun _=>0)
    (fun x=>by simpa using floor x) site
  exact (Nat.le_add_right 1 _).trans ((Nat.le_add_right _ _).trans root)

omit [Fintype F] in
/-- The literal assembler, local S43 weights and exact program length after
transporting from the analysis lane count to the input trace. -/
theorem pathOnLanes (h : (R).plan.History) (start : A.Site→ℕ)
    (smallTiles : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤V)
    (largeTiles : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤V)
    (peak : ∀ z,(R).chargeAt h (B.chargeOnLanes u rem A budget) start z≤V) :
    let C:=B.chargeOnLanes u rem A budget
    (R).LocalFloor C ∧ (R).StageLength (P).length ∧
      (R).FreshPath (B.localCoefficient*(W+1)^3) h (J).steps C start := by
  subst lanes
  let X:=(P).run rem A
  let C:=B.charges (u^8) rem A
  have room : X.LevelsCapped 1 V h C start := by
    apply X.levels_capped_of_terminal h C start 1 V
    intro z
    rw [Nat.mul_one]
    exact peak z
  exact ⟨(P).certified_floor _ (B.factor_bound _) rem A,(P).stageLength_run rem A,
    B.program_fresh_path (Pins:=Pins) u P (B.repeat_supported _) _ (B.factor_bound _) rem A
      smallTiles largeTiles h start room⟩

omit [Fintype F] in
/-- The real terminal factor and its complete pin namespace are bounded by the
unscaled site charge. Both estimates precede native execution and slot selection. -/
theorem rootSizesOnLanes (h : (R).plan.History) (L : A.Words Pins) (ordered : A.OrderedHalves L)
    (N : Forest F L.ports.form) (start : A.Site→ℕ)
    (seeds : ∀ x,1+A.incidentWidth x≤ start x ∧ L.ports.form.width x≤2*start x ∧ (N x).resources≤ start x)
    (smallTiles : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤V)
    (largeTiles : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤V)
    (peak : ∀ z,(R).chargeAt h (B.chargeOnLanes u rem A budget) start z≤V)
    (site : ((R).plan.finish h).Site) :
    let result:=(R).plan.assemble h (J L) N
    let tree:=result.2 site
    let charge:=(R).chargeAt h (B.chargeOnLanes u rem A budget) start site
    tree.compile.cells+tree.compile.internal≤B.terminalRowRate u B.localCoefficient*charge ∧
      result.1.width site≤2*charge := by
  let C:=B.chargeOnLanes u rem A budget
  obtain ⟨floor,length,priced⟩:=B.pathOnLanes (Pins:=Pins) u rem A budget h start smallTiles largeTiles peak
  have local2:2≤B.localCoefficient:=by unfold localCoefficient;omega
  have scale : 2≤B.localCoefficient*(W+1)^3 :=
    local2.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have paid:=(R).assembled_resources h (J).steps C floor L ordered N start (fun x=>(seeds x).1)
    (fun x=>(seeds x).2.1) (B.localCoefficient*(W+1)^3) scale priced
    (fun x=>(seeds x).2.2.trans (Nat.le_mul_of_pos_left _ (by omega))) _ length site
  let T:=((R).plan.assemble h (J L) N).2 site
  have sizes : T.compile.cells+T.compile.internal≤T.resources:=by
    have counted (rows bits nodes pins : ℕ) : rows + bits ≤ bits + rows + nodes + pins := by omega
    rw [T.compiled_rows, T.compiled_bits]
    exact counted T.rows T.bits T.nodes T.footprint.pins
  exact ⟨sizes.trans paid,(R).assembled_width h (J).steps L N C floor start (fun x=>(seeds x).2.1) site⟩

/-- Admission of each physical root for every pre-tick history and team. The native
node maximum and finite tile widths are the only space parameters. -/
theorem admissionOnLanes (h : (R).plan.History) (L : A.Words Pins) (ordered : A.OrderedHalves L)
    (N : Forest F L.ports.form) (start : A.Site→ℕ)
    (seeds : ∀ x,1+A.incidentWidth x≤ start x ∧ L.ports.form.width x≤2*start x ∧ (N x).resources≤ start x)
    (smallTiles : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤V)
    (largeTiles : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤V)
    (peak : ∀ z,(R).chargeAt h (B.chargeOnLanes u rem A budget) start z≤V)
    (degree unitWork : ℕ) (tariff : B.archiveUnit u B.localCoefficient degree≤unitWork)
    (site : ((R).plan.finish h).Site) :
    let tree:=((R).plan.assemble h (J L) N).2 site
    10000*(tree.compile.cells+tree.compile.internal)≤
      unitWork*(R).chargeAt h (B.chargeOnLanes u rem A budget) start site := by
  obtain ⟨sizes,_⟩:=B.rootSizesOnLanes u rem A budget h L ordered N start seeds smallTiles largeTiles peak site
  calc
    _ ≤ 10000*(B.terminalRowRate u B.localCoefficient*(R).chargeAt h (B.chargeOnLanes u rem A budget) start site) :=
      Nat.mul_le_mul_left _ sizes
    _ = (10000*B.terminalRowRate u B.localCoefficient)*(R).chargeAt h (B.chargeOnLanes u rem A budget) start site:=by ring
    _ ≤ _:=Nat.mul_le_mul_right _ ((B.weighted_rows_le_archiveUnit degree B.localCoefficient).trans tariff)


end
end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction RAM.NavigationNodeRows
open scoped Classical BigOperators
open private resource_step from OAI.ThreeFlat.Diagonal.PhysicalTreeResources
open private uncast_tree_price from OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
noncomputable section

variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l} {R : Move F A D m} {i : Fin R.rules.count}

/-- Quantities used by a paid native visit, tied to the actual S43 entries and
the literal earlier and current stage factors in S44 order. -/
structure Move.ResourceReceipt (K height cap : ℕ) (b : Banks) (mem : ℕ→ℕ) (L : A.Words Pins)
    (s : R.WordStep Pins L i) (old : A.ArchiveSites) (fresh : (R.next i).Site→ℕ)
    (row : R.ArchiveStep i old fresh) where
  depth : ℕ
  level : depth<height
  prev : A.Site→ℕ
  pairs : A.Site→ℕ
  before : old.Charged b mem prev pairs
  after : row.sites.Charged b mem (R.push i fresh prev)
    (fun v=>∑ x : {x // R.parent i x=v},pairs x.val)
  oldCap : ∀ x,b.unitWork*prev x≤cap
  newCap : ∀ x,b.unitWork*R.push i fresh prev x≤cap
  priorFloor : ∀ x,1+A.incidentWidth x≤prev x
  nextFloor : ∀ x,1+(R.next i).incidentWidth x≤R.push i fresh prev x
  oldWidth : ∀ x,L.ports.form.width x≤2*prev x
  width : ∀ x,s.words.ports.form.width x≤2*R.push i fresh prev x
  localPrice : ∀ x,s.stage.freshResources ((Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm x)≤K*R.push i fresh prev x
  trees : Forest F L.ports.form
  oldTrees : ∀ x,(trees x).resources≤Run.treeFee K depth*prev x
  currentTrees : ∀ x,(s.nextForest trees x).resources≤Run.treeFee K (depth+1)*R.push i fresh prev x
  assemble : ∀ N : Forest F L.ports.form, (∀ x,(N x).resources≤Run.treeFee K depth*prev x) →
    ∀ x,(s.nextForest N x).resources≤Run.treeFee K (depth+1)*R.push i fresh prev x

/-- The selected stage's S43 floors and row caps bound every edge in
each state by its source's actual work entry. -/
theorem Move.ResourceReceipt.maxWidths {K height cap : ℕ} {b : Banks} {mem : ℕ→ℕ} {L : A.Words Pins}
    {s : R.WordStep Pins L i} {O : A.ArchiveSites} {fresh : (R.next i).Site→ℕ}
    {row : R.ArchiveStep i O fresh} (pay : R.ResourceReceipt K height cap b mem L s O fresh row)
    {volume : ℕ} (unit : 0<b.unitWork) (capFit : cap≤volume) :
    A.maxWidth≤volume ∧ (R.next i).maxWidth≤volume := by
  constructor
  · apply A.maxWidth_le_incident_bound
    intro x
    exact (show A.incidentWidth x≤pay.prev x by have:=pay.priorFloor x;omega).trans
      ((Nat.le_mul_of_pos_left _ unit).trans ((pay.oldCap x).trans capFit))
  · apply (R.next i).maxWidth_le_incident_bound
    intro x
    exact (show (R.next i).incidentWidth x≤R.push i fresh pay.prev x by have:=pay.nextFloor x;omega).trans
      ((Nat.le_mul_of_pos_left _ unit).trans ((pay.newCap x).trans capFit))

def Run.resourceVisit (F Pins : Type) [Field F] (K height cap : ℕ) (b : Banks) (mem : ℕ→ℕ) : Run.WordVisit F Pins :=
  fun _ _ L s O q row=>Nonempty (Move.ResourceReceipt K height cap b mem L s O q row)

private theorem priced_forest {L : A.Words Pins} (s : R.WordStep Pins L i) (N : Forest F L.ports.form) (x : (R.next i).Site) :
    (s.nextForest N x).resources=(s.stage.assemble N ((Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm x)).resources :=
  uncast_tree_price (R.target_eq i).symm s.words.ports.form (s.stage.assemble N) x Tree.resources

private theorem capped_here (r : Run F A) (h : r.plan.History) (C : r.Charges) (start : A.Site→ℕ) (unit cap : ℕ)
    (room : r.LevelsCapped unit cap h C start) : ∀ x,unit*start x≤cap := by
  cases r with
  | done=>exact room
  | step=>exact room.1

/-- Exact charged S43 record and physical typed forest bound at a genuine lookup index. -/
def Run.PricedAt {E : Type} (b : Banks) (mem : ℕ→ℕ) (K height cap idx : ℕ) (node : Run.SelectedNode F Pins E) : Prop :=
  ∃ depth amount,depth≤height ∧ archiveColumn b mem idx 0=b.unitWork*amount ∧ b.unitWork*amount≤cap ∧
    node.arity≤2*amount ∧ node.tree.resources≤Run.treeFee K depth*amount

/-- Enrich every real word visit of the charged archive path with its actual
old and newly assembled forests and the corresponding per-site prices. -/
private theorem Run.typedTraversal (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (ordered : A.OrderedHalves L) (trees : Forest F L.ports.form)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (b : Banks) (mem : ℕ→ℕ) (store : r.ArchiveRowsStored b mem h C O p)
    (K height cap depth n : ℕ) (length : r.StageLength n) (fits : depth+n≤height)
    (start pairs : A.Site→ℕ) (seed : O.Charged b mem start pairs) (scale : 2≤K)
    (floor : r.LocalFloor C) (lo : ∀ x,1+A.incidentWidth x≤ start x)
    (width : ∀ x,L.ports.form.width x≤2*start x) (forest : ∀ x,(trees x).resources≤treeFee K depth*start x)
    (room : r.LevelsCapped b.unitWork cap h C start) (prices : r.FreshPath K h J C start) :
    r.WordVisits (resourceVisit F Pins K height cap b mem) h J L C O p ∧
    ∀ {E : Type} (orig : ∀ x,Fin (L.ext x)→E),r.NodeSteps (PricedAt b mem K height cap) h J L trees C O p orig := by
  induction r generalizing depth n with
  | done=>exact ⟨trivial,fun _=>trivial⟩
  | step R next ih=>
    cases n with
    | zero=>exact False.elim length
    | succ n=>
      let t:=h.1
      let rest:=tailHistory R next h
      let s:=J.1 L t
      let after:=R.push t (C.1 t) start
      let ext:=fiberMass (R.parent t) pairs
      have charged:=p.1.charged b mem start pairs seed store.1
      have base : ∀ x,1+(R.next t).incidentWidth x≤after x:=
        fun x=>((floor t).1 x).trans (Nat.le_add_right ..)
      have nextWidth : ∀ x,s.words.ports.form.width x≤2*after x:=s.width_push start (C.1 t) width (floor t).1
      have every (N : Forest F L.ports.form) (old : ∀ y,(N y).resources≤treeFee K depth*start y) (x : (R.next t).Site) :
          (s.nextForest N x).resources≤treeFee K (depth+1)*after x := by
        rw [priced_forest]
        have paid:=resource_step s N start (C.1 t) scale old width x (prices.1 L ordered lo x)
        convert paid using 1; dsimp only [treeFee,after]; ring
      have nextCap:=capped_here _ rest _ after _ _ room.2
      have tail:=ih t rest (J.2 t) s.words s.halves (s.nextForest trees) (C.2 t) p.1.sites p.2 store.2.2
        (depth+1) n (length t) (by omega) after ext charged (floor t).2 base nextWidth
        (every trees forest) room.2 prices.2
      refine ⟨⟨⟨⟨depth,by omega,start,pairs,seed,charged,room.1,nextCap,lo,base,
        width,nextWidth,prices.1 L ordered lo,trees,forest,every trees forest,every⟩⟩,tail.1⟩,?_⟩
      intro E orig
      refine ⟨?_,tail.2 (pushedOrigin s orig)⟩
      intro x _
      exact ⟨depth+1,after x,by omega,(charged x).1,nextCap x,nextWidth x,every trees forest x⟩

/-- Enrich every real word visit of the charged archive path with its actual
old and newly assembled forests and the corresponding per-site prices. -/
theorem Run.resourceVisits (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (ordered : A.OrderedHalves L) (trees : Forest F L.ports.form)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (b : Banks) (mem : ℕ→ℕ) (store : r.ArchiveRowsStored b mem h C O p)
    (K height cap depth n : ℕ) (length : r.StageLength n) (fits : depth+n≤height)
    (start pairs : A.Site→ℕ) (seed : O.Charged b mem start pairs) (scale : 2≤K)
    (floor : r.LocalFloor C) (lo : ∀ x,1+A.incidentWidth x≤ start x)
    (width : ∀ x,L.ports.form.width x≤2*start x) (forest : ∀ x,(trees x).resources≤treeFee K depth*start x)
    (room : r.LevelsCapped b.unitWork cap h C start) (prices : r.FreshPath K h J C start) :
    r.WordVisits (resourceVisit F Pins K height cap b mem) h J L C O p :=
  (r.typedTraversal h J L ordered trees C O p b mem store K height cap depth n length fits start pairs
    seed scale floor lo width forest room prices).1

/-- Enrich every real word visit of the charged archive path with its actual
old and newly assembled forests and the corresponding per-site prices. -/
theorem Run.selectedAt_priced (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (ordered : A.OrderedHalves L) (trees : Forest F L.ports.form)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (b : Banks) (mem : ℕ→ℕ) (store : r.ArchiveRowsStored b mem h C O p)
    (K height cap depth n : ℕ) (length : r.StageLength n) (fits : depth+n≤height)
    (start pairs : A.Site→ℕ) (seed : O.Charged b mem start pairs) (scale : 2≤K)
    (floor : r.LocalFloor C) (lo : ∀ x,1+A.incidentWidth x≤ start x)
    (width : ∀ x,L.ports.form.width x≤2*start x) (forest : ∀ x,(trees x).resources≤treeFee K depth*start x)
    (room : r.LevelsCapped b.unitWork cap h C start) (prices : r.FreshPath K h J C start) :
    ∀ {E : Type} (orig : ∀ x,Fin (L.ext x)→E) (idx : ℕ) (lo hi),
      PricedAt b mem K height cap idx (r.selectedAt h J L trees C O p orig idx lo hi) := by
  intro E orig idx loIdx hiIdx
  refine r.selectedAt_induction h J L trees C O p orig (PricedAt b mem K height cap) ?_ ?_ idx loIdx hiIdx
  · intro x
    exact ⟨depth,start x,by omega,(seed x).1,capped_here _ h _ _ _ _ room x,width x,forest x⟩
  · exact (r.typedTraversal h J L ordered trees C O p b mem store K height cap depth n length fits start pairs
    seed scale floor lo width forest room prices).2 orig

theorem Run.PricedAt.horizon {E : Type} {b : Banks} {mem : ℕ→ℕ} {K height cap idx : ℕ} {node : Run.SelectedNode F Pins E}
    (h : Run.PricedAt b mem K height cap idx node) (live : 0<b.unitWork) :
    node.tree.resources≤Run.treeFee K height*(archiveColumn b mem idx 0/b.unitWork) := by
  obtain ⟨depth,amount,le,eqn,_,_,size⟩:=h
  rw [eqn,Nat.mul_div_cancel_left _ live]
  apply size.trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega : 2*depth+1≤2*height+1))


end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage.Move.ResourceReceipt
open HistoryContraction RAM RAM.NavigationNodeRows
noncomputable section
variable {F Pins : Type} [Field F] {u K height d l D m : ℕ} {A : State d l} {R : Move F A D m}
    {i : Fin R.rules.count} {L : A.Words Pins} {s : R.WordStep Pins L i} {O : A.ArchiveSites}
    {fresh : (R.next i).Site→ℕ} {row : R.ArchiveStep i O fresh} {b : Banks} {mem : ℕ→ℕ}
local notation "V" => 2^(u^10)
local notation "peak" => 2^((3*u^10+4)/5)
variable (r : Move.ResourceReceipt K height (2^((3*u^10+4)/5)) b mem L s O fresh row)

private theorem slab_fee {j : ℕ} (le : j≤height+1) (fee : 10*(height+2)^2*K≤b.unitWork) :
    10*(j+1)^2*1*K≤b.unitWork := by
  rw [Nat.mul_one]
  apply (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (by omega : j+1≤height+2) 2))).trans fee

theorem old_slab (age : 2≤u) (scale : 2≤K) (fee : 10*(height+2)^2*K≤b.unitWork) (x : A.Site) :
    8*(r.trees x).rows≤V ∧ (r.trees x).bits+L.ext x+L.ports.halfBits x≤V ∧
    (r.trees x).ChildrenFit V ∧ 8*(r.trees x).resources≤V :=
  HistoryStageBody.StageRun.tree_scratch_at_peak age (r.trees x) (r.oldTrees x)
    ((r.oldWidth x).trans (Nat.mul_le_mul_right _ scale)) (le_refl 1)
    (slab_fee (j:=r.depth) (by have:=r.level;omega) fee) (r.oldCap x)

theorem current_slab (age : 2≤u) (scale : 2≤K) (fee : 10*(height+2)^2*K≤b.unitWork)
    (N : Forest F L.ports.form) (old : ∀ x,(N x).resources≤Run.treeFee K r.depth*r.prev x) (x : (R.next i).Site) :
    let T:=s.nextForest N x
    8*T.rows≤V ∧ T.bits+s.words.ext x+s.words.ports.halfBits x≤V ∧ T.ChildrenFit V ∧ 8*T.resources≤V :=
  HistoryStageBody.StageRun.tree_scratch_at_peak age (s.nextForest N x) (r.assemble N old x)
    ((r.width x).trans (Nat.mul_le_mul_right _ scale)) (le_refl 1)
    (slab_fee (j:=r.depth+1) (by have:=r.level;omega) fee) (r.newCap x)


end
end ThreeFlat.Diagonal.PhysicalStage.Move.ResourceReceipt

namespace ThreeFlat.Diagonal.PhysicalStage.Run.PricedAt
open HistoryContraction RAM RAM.NavigationNodeRows
noncomputable section
variable {F Pins E : Type} [Field F] {u K height idx : ℕ} {b : Banks} {mem : ℕ→ℕ}
    {node : Run.SelectedNode F Pins E}
local notation "V" => 2^(u^10)
local notation "peak" => 2^((3*u^10+4)/5)

/-- Every genuine chronological lookup fits its S12 slab, including embedded
children and its complete external and internal word namespaces. -/
theorem slab (p : Run.PricedAt b mem K height peak idx node) (age : 2≤u) (scale : 2≤K)
    (tariff : 10*(height+2)^2*K≤b.unitWork) :
    8*node.tree.rows≤V ∧ node.tree.bits+node.external+node.words.ports.halfBits node.site≤V ∧
      node.tree.ChildrenFit V ∧ 8*node.tree.resources≤V := by
  obtain ⟨depth,amount,level,_,bound,width,resources⟩:=p
  have fee : 10*(depth+1)^2*1*K≤b.unitWork:=by
    rw [Nat.mul_one]
    apply (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (by omega : depth+1≤height+2) 2))).trans tariff
  exact HistoryStageBody.StageRun.tree_scratch_at_peak age node.tree resources
    (width.trans (Nat.mul_le_mul_right _ scale)) (le_refl 1) fee bound

theorem native_words (p : Run.PricedAt b mem K height peak idx node) (age : 2≤u) (scale : 2≤K)
    (tariff : 10*(height+2)^2*K≤b.unitWork) :
    8*node.net.cells≤V ∧ node.external≤V ∧ node.net.internal+node.arity≤V := by
  obtain ⟨rows,words,_,_⟩:=p.slab age scale tariff
  change 8*node.tree.compile.cells ≤ V ∧ node.external ≤ V ∧
    node.tree.compile.internal+(node.external+node.words.ports.halfBits node.site) ≤ V
  rw [node.tree.compiled_rows, node.tree.compiled_bits]
  omega


end
end ThreeFlat.Diagonal.PhysicalStage.Run.PricedAt

namespace ThreeFlat.Diagonal.PhysicalStage.Run.PricedAt
open RAM.NavigationNodeRows RAM.HistoryStageBody.Physical HistoryContraction
noncomputable section
variable {F Pins E : Type} [Field F] [Fintype F] {u K height cap idx : ℕ} {b : Banks} {mem : ℕ→ℕ}
    {node : Run.SelectedNode F Pins E}

/-- Direct page estimate at the S43 weight of every selected chronological
lookup, even for a node with zero incidence width. -/
theorem grid_pages (p : Run.PricedAt b mem K height cap idx node) (B : Block F) {g : Grid F}
    (placed : g∈grids B) (degree : ℕ) (live : 0<b.unitWork)
    (tariff : B.archiveUnit u B.localCoefficient degree≤b.unitWork) :
    gridPageRate (arity B) g*((archiveColumn b mem idx 0/b.unitWork+1)*(16*u^10+1)^3)≤cap := by
  obtain ⟨depth,amount,_,eqn,available,_,tree⟩:=p
  rw [eqn,Nat.mul_div_cancel_left _ live]
  have positive : 1≤amount := by
    have nodeLive:=node.tree.nodes_pos
    by_contra small
    have empty : amount=0:=by omega
    rw [empty,Nat.mul_zero] at tree
    change node.tree.bits+node.tree.rows+node.tree.nodes+node.tree.footprint.pins≤0 at tree
    omega
  exact B.grid_page_margin placed positive tariff available


end
end ThreeFlat.Diagonal.PhysicalStage.Run.PricedAt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PhysicalStage RAM.NavigationNodeRows
noncomputable section
variable {F Pins : Type} [Field F] {K W : ℕ} {cur : Word W} (q : RefreshReceipt F K cur)

theorem funded_widths {fee levels cap v : ℕ} {b : Banks} {mem : ℕ→ℕ} {words : q.input.Words Pins}
    (pay : q.move.ResourceReceipt fee levels cap b mem words (q.wordStep words) q.old q.charge q.step)
    (unit : 0<b.unitWork) (capFit : cap≤v) :
    q.input.maxWidth≤v ∧ ((refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn).next q.branch).maxWidth≤v := by
  have sel:=pay.maxWidths unit capFit
  refine ⟨sel.1,?_⟩
  have transport {a l D D' L : ℕ} {A : State a l} (e : D=D') (R : Move F A D L) (j : Fin R.rules.count) :
      ((Program.recastMove e R).next (Program.degreeTerm e R j)).maxWidth=(R.next j).maxWidth:=by cases e;rfl
  exact (transport q.degreeEq _ q.branch).symm.trans_le sel.2

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

end OAI
