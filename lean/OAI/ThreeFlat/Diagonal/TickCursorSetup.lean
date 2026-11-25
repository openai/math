import OAI.ThreeFlat.RAM.HistorySelectedInterior
import OAI.ThreeFlat.Diagonal.PhysicalNodeCountSpace
import OAI.ThreeFlat.Diagonal.NavigationRootBranches
import OAI.ThreeFlat.Diagonal.TracePrototypeImage
import OAI.ThreeFlat.Diagonal.TickRuntimeBudget
import OAI.ThreeFlat.Diagonal.NavigationResources
import OAI.ThreeFlat.Diagonal.FoldPhysicalClock
import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.RAM.TickTerminalPrepare
import OAI.ThreeFlat.RAM.TickLinkedProgram
import OAI.ThreeFlat.RAM.TickScaleSpace

namespace OAI
/-! # The actual H cursor's physical tick configuration -/
namespace ThreeFlat.Diagonal.TickCursorSetup
open Computability.VPVNP.BurstRAM RAM NavigationPass HistoryStageBody.Physical TraceStaticRow TickWorkspace
open scoped Fin.CommRing BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F]

structure Knobs (W : ℕ) where
  rem : ℕ
  nav : NavigationPass.Parameters
  atom : TraceBucketAtom.Layout
  wireStart : ℕ
  wirePrefix : ℕ
  publicWords : Fin TraceEndpointROM.params→Word W
  startup : TracePrototypeBoot.Args W

/-- The same H machine image and public parameter concatenation determine every
operand of the positive tick: the two clocks, both terminal edge addresses,
the finite H row template, the seed effect codebook, and the X-table suffix. -/
def ofImage (B : PhysicalStage.Block F) (u tariff unitWork : ℕ) (s : PhysicalPinsExpr.Shape)
    (I : PhysicalPrelude.Image F (16*u^10)) (stH : Word (16*u^10)) (hF : Fintype.card F≤2^(16*u^10))
    (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1)) : Knobs (16*u^10) :=
  let W:=16*u^10
  let raw:=I.sizes.rawCount
  let low:=u^10/2
  let steps:=(B.repeat (u^8)).charge
  let rem:=FoldTrace.hDepth u tariff raw-low-steps
  let q:=steps+rem-1
  let d:=(q+1)+low
  let f:=FoldTrace.hFuel u tariff
  let S:=FoldTrace.hHeader u raw
  let G:=gateTable hF hw hp raw f stH u u d
  let atom:=TraceBitHeader.bucketShape (S:=S) (f:=f) (q:=q) (low:=low) hF hw hp raw stH u u
    B.cursorCopies (base u 52) (base u 56) (base u 55) (base u 54)
  let p:=Parameters.cursor B u rem low atom.shape.stride G.cells s 0 unitWork
  let A:=p.archive (2^(B.exponent 0)) W
  let dir:=(B.repeat (u^8)).directory rem A.axes
  let root:=p.rootArchive A (p.nodeArchive A dir W) dir W
  let terminal:=A.terminal dir (root.rootCount*A.initialDegree) W
  let navWords:=Parameters.gridWords B u++p.staticWords B (u^8) rem W
  let pb:=2+I.advice+s.teamBits+s.timeBits
  let n:=G.cells+2*(1+2*d)
  let setup:=TracePrototypeBoot.cursor u pb navWords.length S (TraceUniformRow.SharedCount W u u u d f)
    n G (FieldCode.ofCardLe hF)
  let table:=setup.seedSource+W*(2*n)
  let o:=TraceSuffixOracle.layout I (TraceSuffixOracle.locations W u u u u 2 pb table raw)
  ⟨rem,p,atom,terminal.oldSource,terminal.prefixBase,
    TraceEndpointROM.data atom (fun _=>0) (fun i=>(o.fields i:Word W)) S I.endpointBits low,setup⟩

def hidden (u : ℕ) := TraceVolume.cap u/40000
def cells (u : ℕ) := 2*hidden u

def Knobs.navigation (u : ℕ) (K : Knobs (16*u^10)) (B : PhysicalStage.Block F) :=
  K.nav.machine (W:=16*u^10) B (u^8) K.rem

def Knobs.prepare (u : ℕ) (K : Knobs (16*u^10)) (p : ℕ) (B : PhysicalStage.Block F) (field : FieldCode F (16*u^10)) :=
  TickTerminalRoot.prepare field u p (hidden u) (cells u) K.wireStart K.wirePrefix
    (archive B (base u 38) (16*u^10) B.alphabetCap) K.atom K.publicWords (families B (base u 38) (16*u^10)) K.startup

set_option maxHeartbeats 2000000 in
/-- The compiled header shift, navigation, and selected preparation all have
text sizes bounded by one finite constant depending only on the fixed grid family. -/
theorem text_room (B : PhysicalStage.Block F) :
    ∃ C : ℕ, ∀ u tariff unitWork (s : PhysicalPinsExpr.Shape)
      (I : PhysicalPrelude.Image F (16*u^10)) (stH : Word (16*u^10)) (hF : Fintype.card F≤2^(16*u^10))
      (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1)) (pins : ℕ) (field : FieldCode F (16*u^10)),
      C≤u →
      let K:=ofImage B u tariff unitWork s I stH hF hw hp
      let nv:=K.navigation u B
      let pr:=K.prepare u pins B field
      TickMachine.textCutoff F nv.labels pr.labels nv.registers pr.registers nv.slots pr.slots≤u ∧
      37+(3400+9*(Fintype.card F*Fintype.card F)+nv.labels+pr.labels)≤u ∧
      6+TickPublicData.count nv.slots pr.slots≤u := by
  obtain ⟨navN,nav⟩:=Parameters.cursor_machine_resources B
  obtain ⟨prepN,prep⟩:=TickTerminalRoot.block_prepare_resources B
  refine ⟨3437+9*(Fintype.card F*Fintype.card F)+navN+prepN,?_⟩
  intro u tariff unitWork s I stH hF hw hp pins field age K nv pr
  apply TickMachine.shifted_text_room (navBound:=navN) (prepBound:=prepN) _ _ age
  · exact nav u K.rem (u^10/2) K.atom.shape.stride K.atom.slots s 0 unitWork (16*u^10) (u^8) K.rem
  · exact prep (base u 38) (16*u^10) B.alphabetCap (16*u^10) u pins (hidden u) (cells u)
      K.wireStart K.wirePrefix field K.atom K.publicWords K.startup

theorem word_bounds {u nt ns np teams capacity : ℕ} (age : TraceVolume.cm≤u) (big : 16≤u)
    (exponent : 154≤u) (idBits : nt+ns+np≤u^153) (field : Fintype.card F*Fintype.card F≤u) :
    let q:=2^(u^3)
    let a:=2^(u^10-u^4)
    let p:=ApproximateImage.pinCount q nt ns np a
    ∃ fit : RAM.Contraction.Fits (TickWeightedBank.shape F p (hidden u) (cells u)) (16*u^10),
      TickActiveROM.WordBounds (TickPhysicalABI.mounted u a teams capacity q nt ns np) fit := by
  have power : 1≤u^153 := Nat.one_le_pow _ _ (by omega)
  have params : 2+nt+ns+np≤u^154:=by
    rw [show 154=153+1 from rfl,pow_succ]
    have mult:=Nat.mul_le_mul_left (u^153) (show 3≤u by omega)
    omega
  exact TickPhysicalABI.mounted_space age big exponent params field

omit [Field F] [Fintype F] in
/-- The typed roots in one actual greedy slot pay for its hidden and padded
cell bounds under the same charge used for their native replay. -/
theorem root_padding {ι : Type*} {p : ℕ} (u : ℕ) (ids : List ι) (cost : ι→ℕ)
    (nets : Fin ids.length→BitNetwork F p)
    (pay : ∀ i,10000*((nets i).cells+(nets i).internal)≤cost (ids.get i))
    (slot : (ids.map cost).sum≤TraceVolume.cap u/4) :
    (TickSlotForest.network nets).internal≤hidden u ∧
    (TickSlotForest.network nets).cells+(hidden u-(TickSlotForest.network nets).internal)≤cells u := by
  apply TickSlotForest.padding_fits
  apply (Finset.sum_le_sum (fun i _=>pay i)).trans
  have eq : (∑ i : Fin ids.length,cost (ids.get i))=(ids.map cost).sum := by
    calc
      _ = (List.ofFn (cost ∘ ids.get)).sum := List.sum_ofFn.symm
      _ = ((List.ofFn ids.get).map cost).sum := by rw [List.map_ofFn]
      _ = _ := by rw [List.ofFn_get]
  rwa [eq]

/-- The only field-dependent constant here is the physical coefficient-table
initializer. The virtual H prototype, chronological scan, root lookup, and
remaining deterministic empty-row padding are all included in this cap. -/
def overhead (F : Type*) [Fintype F] :=
  500+8*(TickTerminalPadding.tables F+2)*(6*(8*(TickTerminalPadding.tables F+2))+10)

omit [Field F] in
private theorem admin_le_work {u nodes nroots live : ℕ} (hu : 1≤u)
    (sites : nodes≤2^(u^10-u^4)) (rootSites : nroots≤nodes) (liveRoots : live≤nroots) :
    2*u^152+17+24*nodes+28+11*nroots+7*live+TickTerminalPadding.budget F 0 0≤
      overhead F*u^152*2^(u^10-u^4) := by
  let pow:=u^152
  let chunk:=2^(u^10-u^4)
  let admin:=TickTerminalPadding.budget F 0 0
  change 2*pow+17+24*nodes+28+11*nroots+7*live+admin≤overhead F*pow*chunk
  have hp : 1≤pow:=Nat.one_le_pow _ _ (by omega)
  have hc : 1≤chunk:=Nat.two_pow_pos _
  have a1 : pow≤pow*chunk:=by simpa using Nat.mul_le_mul_left pow hc
  have a2 : chunk≤pow*chunk:=by simpa using Nat.mul_le_mul_right chunk hp
  have a3 : 1≤pow*chunk:=hp.trans a1
  have sizes : nodes≤chunk:=sites
  calc
      _ ≤ 2*(pow*chunk)+42*(pow*chunk)+(45+admin)*(pow*chunk) := by
        have hbase:=Nat.mul_le_mul_left (45+admin) a3
        omega
      _ = (admin+89)*(pow*chunk) := by ring
      _ ≤ _ := by
        rw [Nat.mul_assoc (overhead F) pow chunk]
        apply Nat.mul_le_mul_right
        dsimp [admin,overhead,TickTerminalPadding.budget]
        omega

omit [Field F] in
theorem slot_clock {u nroots nodes live startup selected charged finish inside tail : ℕ}
    {gCells gHidden : ℕ} (fixed : 8*overhead F≤u) (age : 152+1+TraceVolume.cm≤u)
    (sites : nodes≤2^(u^10-u^4)) (rootSites : nroots≤nodes) (liveRoots : live≤nroots)
    (boot : startup≤2*u^152) (walk : selected≤17+24*nodes+charged)
    (joint : let m:=TraceVolume.cap u
      let H:=hidden u
      let J:=cells u
      let b:=H-gHidden
      let q:=J-(gCells+b)
      charged+finish≤28+11*nroots+7*live+(m/4)/4+TickTerminalPadding.budget F b q)
    (prepares : inside≤ startup+selected) (finishes : tail≤finish) :
    inside+tail≤TraceVolume.cap u/4 := by
  let chunk:=2^(u^10-u^4)
  let m:=TraceVolume.cap u
  let pow:=u^152
  let admin:=TickTerminalPadding.budget F 0 0
  let b:=hidden u-gHidden
  let q:=cells u-(gCells+b)
  have hu : 1≤u:=by omega
  have fmajor:=admin_le_work (F:=F) hu sites rootSites liveRoots
  change 2*pow+17+24*nodes+28+11*nroots+7*live+admin≤overhead F*pow*chunk at fmajor
  have major := TickRuntimeBudget.chunk_quarter (u:=u) (e:=152) (cm:=TraceVolume.cm)
    (C:=2*overhead F) (by omega) age hu
  change 2*overhead F*pow*chunk≤ m/4 at major
  rw [show 2*overhead F*pow*chunk=2*(overhead F*pow*chunk) by ring] at major
  have variablePart : TickTerminalPadding.budget F b q=admin+248*(b+q):=by
    simp [TickTerminalPadding.budget,admin]; omega
  have bcap : b≤hidden u:=Nat.sub_le ..
  have jcap : b+q≤2*(m/40000):=by
    change b≤ m/40000 at bcap
    change b+(2*(m/40000)-(gCells+b))≤_
    omega
  change charged+finish≤28+11*nroots+7*live+(m/4)/4+TickTerminalPadding.budget F b q at joint
  rw [variablePart] at joint
  change startup≤2*pow at boot
  have paid : inside+tail≤overhead F*pow*chunk+(m/4)/4+248*(b+q) := by omega
  have remaining : 248*(b+q)≤(m/4)/4 := by omega
  change inside+tail≤ m/4
  omega

omit [Field F] in
/-- Both procedure clocks are fixed before the RAM input is inspected. The
selected quota is a property of the typed history. Every possible returned
memory pays its finish cost from the same remaining allowance. -/
theorem slot_allowances {u nroots nodes live startup charged gCells gHidden : ℕ}
    (fixed : 8*overhead F≤u) (age : 152+1+TraceVolume.cm≤u)
    (sites : nodes≤2^(u^10-u^4)) (rootSites : nroots≤nodes) (liveRoots : live≤nroots)
    (boot : startup≤2*u^152) (selectedQuota : charged≤(TraceVolume.cap u/4)/4) :
    let m:=TraceVolume.cap u
    let b:=hidden u-gHidden
    let q:=cells u-(gCells+b)
    let joint:=28+11*nroots+7*live+(m/4)/4+TickTerminalPadding.budget F b q
    let inside:=startup+(17+24*nodes+charged)
    let tail:=joint-charged
    inside+tail≤ m/4 ∧ ∀ actual, charged+actual≤joint → actual≤tail := by
  intro m b q joint inside tail
  have budget : charged≤joint:=by dsimp [joint];omega
  refine ⟨slot_clock (F:=F) (gCells:=gCells) (gHidden:=gHidden) fixed age sites rootSites liveRoots boot
    (selected:=17+24*nodes+charged) (walk:=le_rfl)
    (joint:=show charged+tail≤joint by dsimp [tail];omega)
    (inside:=inside) (tail:=tail) (prepares:=le_rfl) (finishes:=le_rfl),?_⟩
  intro actual cap
  dsimp [tail]
  omega

omit [Field F] in
/-- A pair of completely uniform clocks for CursorSlot. The selected costs
and the subtree ownership proof may vary with the witnessing archive; both
native procedures still have a common bound over every such memory. -/
theorem uniform_clocks {u nroots nodes live startup walk charged finish gHidden gCells : ℕ}
    (fixed : 32*overhead F≤u) (age : 152+1+TraceVolume.cm≤u)
    (sites : nodes≤2^(u^10-u^4)) (rootSites : nroots≤nodes) (liveRoots : live≤nroots)
    (boot : startup≤2*u^152) (visit : walk≤17+24*nodes+charged)
    (price : charged≤(TraceVolume.cap u/4)/4)
    (total : let m:=TraceVolume.cap u
      let b:=hidden u-gHidden
      let q:=cells u-(gCells+b)
      finish≤28+11*nroots+7*live+(m/4)/4+TickTerminalPadding.budget F b q) :
    let m:=TraceVolume.cap u
    startup+walk≤ m/8 ∧ finish≤ m/8 ∧ m/8+m/8≤ m/4 := by
  intro m
  have hu : 1≤u:=by omega
  let b:=hidden u-gHidden
  let q:=cells u-(gCells+b)
  have admin:=admin_le_work (F:=F) hu sites rootSites liveRoots
  have time:=TickRuntimeBudget.chunk_quarter (u:=u) (e:=152) (cm:=TraceVolume.cm) (C:=8*overhead F)
    (by omega) age hu
  change 8*overhead F*u^152*2^(u^10-u^4)≤ m/4 at time
  rw [show 8*overhead F*u^152*2^(u^10-u^4)=8*(overhead F*u^152*2^(u^10-u^4)) by ring] at time
  have bcap : b≤ m/40000:=Nat.sub_le ..
  have empty : b+q≤2*(m/40000):=by
    change b+(2*(m/40000)-(gCells+b))≤_
    omega
  change charged≤(m/4)/4 at price
  change finish≤28+11*nroots+7*live+(m/4)/4+TickTerminalPadding.budget F b q at total
  rw [show TickTerminalPadding.budget F b q=TickTerminalPadding.budget F 0 0+248*(b+q) by
    simp [TickTerminalPadding.budget]; omega] at total
  omega

/-- Price the actual terminal iteration from the fields observed in its
decremented native memory. Its endpoint and half-wire counts together equal
the typed root arity and its row count is the compiled trivalent row count. -/
theorem root_iteration_price {W : ℕ} (A : TickTerminalRoot.Arena) (init : Memory W) (i : ℕ)
    (amount rowRate halves arity cells unitWork : ℕ)
    (unit : 1≤amount) (rows : cells≤rowRate*amount) (pins : arity≤2*amount)
    (tariff : TickTerminalRoot.rootFactor*(halves+4*rowRate+3)≤unitWork)
    (counts : let m:=TickTerminalRoot.natMemory (TickTerminalRoot.decrease A (TickTerminalRoot.images A init i))
      let t:=TickTerminalRoot.terminal A m
      t.halves≤halves ∧ t.ext+(∑j:Fin t.halves,(HistoryTerminalTape.half t m j.val).width)=arity ∧ t.rows=cells) :
    TickTerminalRoot.iterationCost A init i≤unitWork*amount := by
  let m:=TickTerminalRoot.natMemory (TickTerminalRoot.decrease A (TickTerminalRoot.images A init i))
  let T:=TickTerminalRoot.terminal A m
  obtain ⟨d,width,cnt⟩:=counts
  have price:=TickTerminalRoot.work_bound W A T m
  have count : TickTerminalPrimitive.words T m=arity+4*cells:=by
    rw [TickTerminalRoot.words_eq,width,cnt]
  have room : halves≤halves*amount:=by simpa using Nat.mul_le_mul_left halves unit
  have halfBound : T.halves≤halves*amount := d.trans room
  have privateRows:=Nat.mul_le_mul_left 4 rows
  have numerator : 1+T.halves+TickTerminalPrimitive.words T m≤(halves+4*rowRate+3)*amount:=by
    rw [count,Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
    omega
  calc
    _ ≤ _ := price
    _ ≤ _ := Nat.mul_le_mul_left _ numerator
    _ = _ := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ tariff

omit [Field F] in
/-- The typed per-root charges cover the actual terminal loop on every returned
memory. Both the visit clock and the terminal clock use the scheduler's same
fixed quota and are bounded separately before the native interpreter starts. -/
theorem selected_pass_clocks {u p n nodes startup elapsed priced : ℕ} {arity : Fin n→ℕ}
    (net : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→Fin p)
    (wireStart wirePrefix : ℕ) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner (16*u^10)) (m : Memory (16*u^10)) (tariff : Fin n→ℕ)
    (fixed : 32*overhead F≤u) (age : 152+1+TraceVolume.cm≤u)
    (sites : nodes≤2^(u^10-u^4)) (roots : head.roots≤nodes) (filtered : n≤head.roots)
    (boot : startup≤2*u^152) (walk : elapsed≤17+24*nodes+priced)
    (price : priced≤(TraceVolume.cap u/4)/4)
    (schedule : (∑ i,tariff i)≤(TraceVolume.cap u/4)/4)
    (iterations : ∀i:Fin n,TickTerminalRoot.iterationCost
      (TickTerminalRoot.mounted u p wireStart wirePrefix) (TickTerminalRoot.rootStart u head own m) i.val≤tariff i) :
    startup+elapsed≤TraceVolume.cap u/8 ∧
      TickTerminalRoot.finishCost (H:=hidden u) (J:=cells u) net wire wireStart wirePrefix head own m≤TraceVolume.cap u/8 := by
  let A:=TickTerminalRoot.mounted u p wireStart wirePrefix
  let init:=TickTerminalRoot.rootStart u head own m
  let cost:=TickTerminalRoot.iterationCost A init
  have sum : (∑ j ∈ Finset.range n,cost (n-(j+1)))=(∑ i:Fin n,cost i.val):=by
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [Nat.sub_sub,Nat.add_comm] using Finset.sum_range_reflect cost n
  have payable : (∑ j ∈ Finset.range n,cost (n-(j+1)))≤(TraceVolume.cap u/4)/4:=
    sum.trans_le ((Finset.sum_le_sum (s:=Finset.univ) (fun i _=>iterations i)).trans schedule)
  let G:=TickTerminalRoot.forest net wire
  let b:=hidden u-G.internal
  let q:=cells u-(G.cells+b)
  have enough : TickTerminalRoot.finishCost (H:=hidden u) (J:=cells u) net wire wireStart wirePrefix head own m≤
      28+11*head.roots+7*n+(TraceVolume.cap u/4)/4+TickTerminalPadding.budget F b q:=by
    change (24+11*head.roots)+(4+7*n+∑ j ∈ Finset.range n,cost (n-(j+1)))+
      TickTerminalPadding.budget F b q≤_
    omega
  have bounds:=uniform_clocks (F:=F) (gHidden:=G.internal) (gCells:=G.cells)
    fixed age sites roots filtered boot walk price enough
  exact ⟨bounds.1,bounds.2.1⟩

/-- The initialized generator and the native selected chronological loop share
the same returned memory. This composes their actual opcodes with the original
input predicate so the seven-phase runtime can call prepare_compiled. -/
theorem selected_after_boot {u q : ℕ} (boot : TracePrototypeBoot.Args (16*u^10))
    (G : BitNetwork F q) (code : FieldCode F (16*u^10)) (keys : Fin q→TraceAddressRecord.Record)
    (es : List (EffectStream.Record (16*u^10))) (B : PhysicalStage.Block F) (K : Knobs (16*u^10))
    (pre post : Memory (16*u^10)→Prop) (allowance : ℕ)
    (seeds : (boot.procedure u).Spec pre (fun m out=>out=boot.image u G code keys es m) boot.budget)
    (interior : ∀ input,pre input → ∃ cost, boot.budget+cost≤allowance ∧
      (selected (16*u^10) u (archive B (base u 38) (16*u^10) B.alphabetCap) K.atom K.publicWords
        (families B (base u 38) (16*u^10))).Spec (·=boot.image u G code keys es input) (fun _ out=>post out) cost) :
    ((boot.procedure u).seq (selected (16*u^10) u (archive B (base u 38) (16*u^10) B.alphabetCap) K.atom
      K.publicWords (families B (base u 38) (16*u^10)))).Spec pre (fun _ out=>post out) allowance := by
  intro pn rn kn M pc reg pub exit rom data cfg input entry ok
  obtain ⟨cost,time,work⟩:=interior input ok
  have seeded : (boot.procedure u).Spec (·=input)
      (fun _ out=>out=boot.image u G code keys es input) boot.budget :=
    PhysicalProcedure.Procedure.Spec.atMemory seeds input ok
  obtain ⟨t,ht,done,out,run,atExit,mid,_,result⟩ :=
    PhysicalProcedure.Procedure.Spec.seq (A:=boot.procedure u)
      (B:=selected (16*u^10) u (archive B (base u 38) (16*u^10) B.alphabetCap)
        K.atom K.publicWords (families B (base u 38) (16*u^10)))
      seeded work (fun _ _ eq=>eq) M pc reg pub exit rom data cfg input entry rfl
  exact ⟨t,ht.trans time,done,out,run,atExit,result⟩

/-- Counts in the deterministic scan come directly from the archived terminal
layer and the physical filter over its root IDs. -/
theorem cursor_count {u rem low stride cells offset tariff : ℕ} (B : PhysicalStage.Block F)
    (s : PhysicalPinsExpr.Shape) (large : 40≤u) (levels : B.levels+1≤u) (coeff : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) :
    let W:=16*u^10
    let p:=Parameters.cursor B u rem low stride cells s offset tariff
    let A:=p.archive (2^(B.exponent 0)) W
    let ss:=(B.repeat (u^8)).directory rem p.axes
    let a:=p.rootArchive A (p.nodeArchive A ss W) ss W
    a.firstFinal+a.rootCount≤2^(u^10-u^4) ∧ a.rootCount≤a.firstFinal+a.rootCount ∧
    ∀ (N : RootArchive.Nodes a) (own : TickSlotLookup.Owner W) (m : Memory W),
      (TickTerminalRoot.rootIds u (a.summaryHeader N) own m).length≤a.rootCount := by
  intro W p A ss a
  have count : 8*(a.firstFinal+a.rootCount)≤2^(u^10-u^4) :=
    (node_count_space B p large levels coeff half depth rfl).2.1
  refine ⟨by omega,Nat.le_add_left ..,?_⟩
  intro N own m
  let looks:=TickTerminalRoot.rootLookup u
  let pred:=TickSlotLookup.matchesOwner own (m looks.s1) (m (looks.s1+3))
  simpa only [TickTerminalRoot.rootIds,TickRootScanInit.chosen,RootArchive.summaryHeader,List.length_range]
    using (List.length_filter_le pred (List.range a.rootCount))

/-- Native S12 streams and inherited terminal endpoints are reserved by the
actual chronological ordinal. The size of the reserved gap adds no RAM steps. -/
theorem root_storage {u total roots seedCount : ℕ} (age : 8≤u)
    (sites : total≤2^(u^10-u^4)) (rootsFit : roots≤total) (i : Fin total)
    {rows ext pins : ℕ} (cellCap : 4*rows≤volume u) (extCap : ext≤volume u) (pinCap : pins≤volume u) :
    8*total ≤ stride u ∧ 2*roots ≤ stride u/4 ∧ 64+pins ≤ stride u ∧
    (base u 12 ≤ streamAt u seedCount i.val ∧ streamAt u seedCount i.val+4*rows≤base u 14) ∧
    (base u 12≤endsAt u seedCount i.val ∧ endsAt u seedCount i.val+ext≤base u 14) := by
  let V:=volume u
  have power : 8≤u^10:=age.trans (Nat.le_self_pow (by decide:10≠0) u)
  have large : 256≤V:=Nat.pow_le_pow_right (by decide:0<2) power
  have growth : total≤V:=sites.trans (Nat.pow_le_pow_right (by decide:0<2) (Nat.sub_le ..))
  have unit : 1≤V:=by omega
  have cubic : V^3 ≤ stride u:=Nat.pow_le_pow_right unit (by decide:3≤4)
  have blocks : 8*total ≤ stride u:=by
    calc 8*total ≤ V*V := Nat.mul_le_mul (by omega) growth
         _ = V^2:=by ring
         _ ≤ V^4:=Nat.pow_le_pow_right unit (by decide)
  have bounds:=address_limits (seedCount:=seedCount) (i:=i.val) (show 162≤volume u by omega) cellCap extCap
  have lastWord : (i.val+1)*V^2 ≤ stride u := by
    calc _ ≤ V*V^2 := Nat.mul_le_mul_right _ (i.isLt.trans_le growth)
         _ = V^3:=by ring
         _ ≤ _:=cubic
  have apart:=TickWorkspace.apart (u:=u) (by decide:12<14)
  have alloc : 64+pins ≤ stride u:=by
    calc _ ≤ 2*V:=by omega
         _ ≤ V*V:=Nat.mul_le_mul_right _ (by omega)
         _ = V^2:=by ring
         _ ≤ V^4:=Nat.pow_le_pow_right unit (by decide)
  have left : base u 12 ≤ streamAt u seedCount i.val:=(Nat.le_add_right ..).trans bounds.1
  have right : streamAt u seedCount i.val≤endsAt u seedCount i.val:=Nat.le_add_right ..
  change (i.val+1)*(volume u)^2 ≤ stride u at lastWord
  refine ⟨blocks,by omega,alloc,⟨left,?_⟩,⟨left.trans right,?_⟩⟩ <;> omega

section Prototype
open LaneCursor LaneCursor.RowLayout
variable {u S fuel q low : ℕ}
local notation "wordWidth" => 16*u^10
local notation "dH" => ((q+1)+low)
variable (hF : Fintype.card F≤2^(16*u^10)) (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1))
    (addr : ℕ) (st : Word (16*u^10)) (hs : S≤2^(16*u^10)) (hf : fuel≤2^(16*u^10+1))
    (grid : S+fuel≤2^(1+((q+1)+low)))
local notation "G" => gateTable hF hw hp addr fuel st u u dH
local notation "K" => TraceBitDescriptor.records (p:=u) (r:=u) (k:=u) (d:=dH) hw addr S fuel
local notation "b" => TickWorkspace.base u
local notation "es" => TraceBitHeader.bankRecords (W:=wordWidth) (q:=q) (low:=low)
  hF hw hp addr st hs hf u u grid (b 54) (b 55) (b 56)
variable (code : FieldCode F (16*u^10)) (pb navLen : ℕ)
local notation "boot" => TracePrototypeBoot.cursor u pb navLen S
  (TraceUniformRow.SharedCount wordWidth u u u dH fuel) (List.length es) G code

private abbrev prototypeMounted {w a : ℕ} (args : TracePrototypeBoot.Args w) (sector : ℕ)
    (table : BitNetwork F a) (codec : FieldCode F w) (keys : Fin a → TraceAddressRecord.Record)
    (seeds : List (EffectStream.Record w)) (src : Memory w) : Prop :=
  (∀ i, src (args.templateSource+i.val)=((FixedTraceImage.parameter table codec keys i).toNat : Word w)) ∧
    EffectSeed.Input args.seedSource sector seeds src

/-- Execute the selected prototype boot on the protected bits returned by
navigation. The three true disjoint seed banks prove the effect scatter safe. -/
theorem startup_spec (age : 2≤u)
    (tableSize : FixedTraceImage.count G≤TickWorkspace.stride u)
    (masks : 1+(dH+dH)≤TickWorkspace.stride u) (rowCount : 2^dH≤TickWorkspace.stride u)
    (count : 2*(es).length≤TickWorkspace.stride u) (lowEnd : (boot).seedSource+wordWidth*(2*(es).length)≤b 53)
    (pre : Memory wordWidth→Prop)
    (mounted : ∀ src,pre src→prototypeMounted boot (b 58) G code K es src) :
    ((boot).procedure u).Spec pre (fun m out=>out=(boot).image u G code K es m) (boot).budget := by
  have step : 60<TickWorkspace.stride u:=by
    have bound : 2≤u^10:=(Nat.le_self_pow (by decide:10≠0) u).trans' age
    have val : 4≤2^(u^10):=Nat.pow_le_pow_right (by decide:0<2) bound
    have pow:=Nat.pow_le_pow_left val 4
    change 60<(2^(u^10))^4
    omega
  have all (i : ℕ) (h : i≤58) := TickWorkspace.word_space (u:=u) (i:=i) (by omega) (by omega)
  have h53:=TickWorkspace.apart (u:=u) (by decide:53<54)
  have h54:=TickWorkspace.apart (u:=u) (by decide:54<55)
  have h55:=TickWorkspace.apart (u:=u) (by decide:55<56)
  have h56:=TickWorkspace.apart (u:=u) (by decide:56<58)
  have rows : 2^(q+1)*2^low≤TickWorkspace.stride u:=by simpa only [pow_add] using rowCount
  have cells : (G).cells≤TickWorkspace.stride u:=by unfold FixedTraceImage.count at tableSize;omega
  have end56:=all 56 (by decide)
  have room : SeedRoom (G).cells (1+(dH+dH)) (2^(q+1)*2^low) (b 54) (b 55) (b 56) wordWidth :=
    ⟨by omega,by omega,by omega⟩
  have safe:EffectStream.Safe (b 58) es := (TraceBitHeader.layout hF hw hp addr st hs hf u u grid).seed_safe
    (b 54) (b 55) (b 56) (b 58) (fun j : Fin (G).cells=>((HistoryCompiledRows.library G).id j).val)
    room (Or.inr (by omega))
  have end53 := (Nat.add_le_add_left tableSize (b 53)).trans_lt (all 53 (by decide))
  have end58 := (Nat.add_le_add_left count (b 58)).trans_lt (all 58 (by decide))
  have end57 : b 57+FixedTraceProgram.P < 2^wordWidth := by
    change b 57+18 < _
    exact (Nat.add_le_add_left (by omega : 18 ≤ TickWorkspace.stride u) (b 57)).trans_lt
      (all 57 (by decide))
  intro labels registers slots machine pc reg pub exit installed data cfg src entry ok
  exact (boot).run u G code K es rfl rfl lowEnd end53 end58 end57 safe
    machine pc reg pub exit installed data cfg src entry (mounted src ok)
end Prototype

/-- The prototype touches only sectors 53 and above. In particular the S1
tick, S5 group intervals, S11 owners, S38 grid, and S44..S49 archive remain
the ones returned by the chronological navigator. -/
theorem startup_preserves {u S fuel q low : ℕ}
    (hF : Fintype.card F≤2^(16*u^10)) (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1))
    (addr : ℕ) (st : Word (16*u^10)) (hs : S≤2^(16*u^10)) (hf : fuel≤2^(16*u^10+1))
    (grid : S+fuel≤2^(1+((q+1)+low))) (code : FieldCode F (16*u^10)) (pb navLen : ℕ)
    (src : Memory (16*u^10)) (z : ℕ) (lowWord : z<TickWorkspace.base u 53)
    (tableSize : FixedTraceImage.count (gateTable hF hw hp addr fuel st u u ((q+1)+low))≤TickWorkspace.stride u)
    (masks : 1+(((q+1)+low)+((q+1)+low))≤TickWorkspace.stride u)
    (rows : 2^((q+1)+low)≤TickWorkspace.stride u)
    (wordFit : TickWorkspace.base u 56+TickWorkspace.stride u≤2^(16*u^10)) :
    let d := (q+1)+low
    let table := gateTable hF hw hp addr fuel st u u d
    let keys := TraceBitDescriptor.records (w:=16*u^10) (p:=u) (r:=u) (k:=u) (d:=d) hw addr S fuel
    let seeds := TraceBitHeader.bankRecords (w:=16*u^10) (W:=16*u^10) (p:=u) (q:=q) (low:=low)
      hF hw hp addr st hs hf u u grid (TickWorkspace.base u 54) (TickWorkspace.base u 55) (TickWorkspace.base u 56)
    let boot := TracePrototypeBoot.cursor u pb navLen S (TraceUniformRow.SharedCount (16*u^10) u u u d fuel)
      seeds.length table code
    boot.image u table code keys seeds src z=src z :=
  TraceBitHeader.prototype_below (u:=u) (S:=S) (fuel:=fuel) (q:=q) (low:=low)
    hF hw hp addr st hs hf grid code pb navLen src tableSize masks rows wordFit z lowWord

end

end ThreeFlat.Diagonal.TickCursorSetup

end OAI
