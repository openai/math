import OAI.Hierarchy.DescentIssuedRangeHistory
import OAI.Hierarchy.DescentNamedRoleDecoded
import OAI.Hierarchy.DescentNamedIssuedTerminalDigits

namespace OAI
/-! # Last-reset range reads at the gate selected by the terminal shelf -/

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentColonies DescentInitialHost
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentPackedSeed DescentMixedRouter DescentResetInvoice DescentTerminalSliceRuns DescentTerminalCombinedRole
open DescentRetainedRangeDigits DescentDatedAddressBook DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false

open DescentLocalArchiveOrder
open private Palette.encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private Palette.readsAtView Palette.branchReadsOfHistory Palette.selectedRotor Palette.selectedBranch from OAI.Hierarchy.DescentNamedRetainedRanges
variable {F : Type} [Field F]

private def sameRegister {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {B : BitDescription W}
    (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    (block : NodeOrder.All B → Fin out.receiver.blocks) (host : NodeOrder.All B → Fin out.receiver.hosts)
    (groupOf : NodeOrder.All B → Fin out.receiver.groups) (number : NodeOrder.All B → Fin out.nodes) (reg : Register B) : Prop :=
  (∃ (live : 0 < out.receiver.lanes) (bs : NodeOrder.All B → Fin out.receiver.blocks)
      (hs : NodeOrder.All B → Fin out.receiver.hosts) (gs : NodeOrder.All B → Fin out.receiver.groups)
      (ns : NodeOrder.All B → Fin out.nodes),
      (∀ x, (bs x).val = (block x).val ∧ (hs x).val = (host x).val ∧
        (gs x).val = (groupOf x).val ∧ (ns x).val = (number x).val) ∧
      reg = fromRAM (PriorResetArchive.reset out offset) out.rangeLayout out.nodeBits m live bs hs gs ns) →
    reg = fromRAM (PriorResetArchive.reset out offset) out.rangeLayout out.nodeBits m pos block host groupOf number

private theorem sameRegisterHolds {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {B : BitDescription W}
    (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    (block : NodeOrder.All B → Fin out.receiver.blocks) (host : NodeOrder.All B → Fin out.receiver.hosts)
    (groupOf : NodeOrder.All B → Fin out.receiver.groups) (number : NodeOrder.All B → Fin out.nodes) (reg : Register B) : sameRegister out offset m pos block host groupOf number reg := by
  rintro ⟨live, bs, hs, gs, ns, measured, found⟩
  have eb : bs = block := funext (fun x => Fin.ext (measured x).1)
  have eh : hs = host := funext (fun x => Fin.ext (measured x).2.1)
  have eg : gs = groupOf := funext (fun x => Fin.ext (measured x).2.2.1)
  have en : ns = number := funext (fun x => Fin.ext (measured x).2.2.2)
  simpa only [eb, eh, eg, en] using found

private theorem ordinal_equiv_value {Y : Type} [Fintype Y] (e:Y≃Fin (Fintype.card Y)) (u:Y) :
    (DescentTerminalChronologicalBooks.ordinal (e.toEmbedding.trans Fin.valEmbedding) u).val=(e u).val := by
  classical
  rw [DescentTerminalChronologicalBooks.ordinal_val]
  let xs := Finset.univ.filter (fun a:Y=>(e a).val<(e u).val)
  change xs.card=(e u).val
  have mapped : xs.map e.toEmbedding=Finset.Iio (e u) := by
    ext t
    constructor
    · intro ht
      obtain ⟨a,ha,eq_⟩:=Finset.mem_map.mp ht
      subst t
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp ha).2
    · intro ht
      refine Finset.mem_map.mpr ⟨e.symm t,?_,e.apply_symm_apply t⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa using Finset.mem_Iio.mp ht⟩
  calc
    xs.card=(xs.map e.toEmbedding).card := by rw [Finset.card_map]
    _=(e u).val := by rw [mapped,Fin.card_Iio]

private def rawAtSite {P U : Type} {depth : ℕ} {bits : P → ℕ} {W : MarkedWorld F depth P bits} {B : BitDescription W}
    (v : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < v.receiver.lanes)
    (bmap : NodeOrder.All B → Fin v.receiver.blocks) (hmap : NodeOrder.All B → Fin v.receiver.hosts)
    (gmap : NodeOrder.All B → Fin v.receiver.groups) (nmap : NodeOrder.All B → Fin v.nodes) (reg : Register B)
    (index : U → NodeOrder.All B) (block : Fin v.receiver.blocks) (host : Fin v.receiver.hosts) (group : Fin v.receiver.groups) (slot : U → Fin v.nodes) : Prop :=
  reg = fromRAM (PriorResetArchive.reset v offset) v.rangeLayout v.nodeBits m pos bmap hmap gmap nmap →
  v.receiver.lanes = v.receiver.groups → v.nodeBits*v.nodes*v.receiver.lanes ≤ w →
  ∀ (u : U) (j : Fin v.argumentSlots) (f : Fin 3) (cells : Fin v.receiver.hosts → Fin v.receiver.groups → Cell (v.nodeBits*v.nodes)),
    Reads (v.terminalField offset (DescentRetainedRangeDigits.page f) j block) cells v.receiver.groups m →
    ((encode v.nodeBits v.nodes).symm (cells host group) (slot u)).val = reg.word (index u) j.val f

private theorem rawAtSiteHolds {P U : Type} {depth : ℕ} {bits : P → ℕ} {W : MarkedWorld F depth P bits} {B : BitDescription W}
    (v : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < v.receiver.lanes)
    (bmap : NodeOrder.All B → Fin v.receiver.blocks) (hmap : NodeOrder.All B → Fin v.receiver.hosts)
    (gmap : NodeOrder.All B → Fin v.receiver.groups) (nmap : NodeOrder.All B → Fin v.nodes) (reg : Register B)
    (index : U → NodeOrder.All B) (block : Fin v.receiver.blocks) (host : Fin v.receiver.hosts) (group : Fin v.receiver.groups) (slot : U → Fin v.nodes)
    (eb : ∀ u, bmap (index u) = block) (eh : ∀ u, hmap (index u) = host)
    (eg : ∀ u, gmap (index u) = group) (en : ∀ u, nmap (index u) = slot u) : rawAtSite v offset m pos bmap hmap gmap nmap reg index block host group slot := by
  intro stored pitch cap u j f cells seen
  have read : Reads (v.terminalField offset (DescentRetainedRangeDigits.page f) j (bmap (index u))) cells v.receiver.lanes m := by
    rw [eb, pitch]; exact seen
  have physical := v.issued_range offset m pos bmap hmap gmap nmap (index u) j f
    (fun n h g => (encode v.nodeBits v.nodes).symm (cells h g) n) (by simpa only [Equiv.apply_symm_apply] using read) cap
  have out := physical.symm.trans (congrArg (fun r : Register B => r.word (index u) j.val f) stored.symm)
  simpa only [eh, eg, en] using out

private def rangeAtSite {P : Type} {d s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B)
    (atSite : W.graph.Site) (history : Prop) (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    (bmap : NodeOrder.All B → Fin out.receiver.blocks) (hmap : NodeOrder.All B → Fin out.receiver.hosts)
    (gmap : NodeOrder.All B → Fin out.receiver.groups) (nmap : NodeOrder.All B → Fin out.nodes) (reg : Register B)
    (block : Fin out.receiver.blocks) (host : Fin out.receiver.hosts) (group : Fin out.receiver.groups)
    (slot : ((enc.view dict).recipe atSite).Node → Fin out.nodes) : Prop :=
  history → reg = fromRAM (PriorResetArchive.reset out offset) out.rangeLayout out.nodeBits m pos bmap hmap gmap nmap →
  out.receiver.lanes = out.receiver.groups → out.nodeBits*out.nodes*out.receiver.lanes ≤ w →
  ∀ (u : ((enc.view dict).recipe atSite).Node), classify G p s (((enc.view dict).recipe atSite).tag u) = .rotor →
  ∀ (fit : (repeatFields (((Encoding.viewShape dict enc sh).sites atSite).sliceFields u).flatten).length ≤ out.argumentSlots)
    (sp : Fin 3 → Fin out.argumentSlots → Fin out.receiver.hosts → Fin out.receiver.groups → Cell (out.nodeBits*out.nodes)),
  (∀ j f, Reads (out.terminalField offset (DescentRetainedRangeDigits.page f) j block) (sp f j) out.receiver.groups m) →
  ∀ (j : Fin (repeatFields (((Encoding.viewShape dict enc sh).sites atSite).sliceFields u).flatten).length) (f : Fin 3),
  ((encode out.nodeBits out.nodes).symm (sp f (j.castLE fit) host group) (slot u)).val =
    atSlot ((Encoding.viewShape dict enc sh).sites atSite) u j.val f

private theorem rangeAtSiteHolds {P : Type} {d s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B)
    (atSite : W.graph.Site) (history : Prop) (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    (bmap : NodeOrder.All B → Fin out.receiver.blocks) (hmap : NodeOrder.All B → Fin out.receiver.hosts)
    (gmap : NodeOrder.All B → Fin out.receiver.groups) (nmap : NodeOrder.All B → Fin out.nodes) (reg : Register B)
    (block : Fin out.receiver.blocks) (host : Fin out.receiver.hosts) (group : Fin out.receiver.groups)
    (slot : ((enc.view dict).recipe atSite).Node → Fin out.nodes)
    (raw : rawAtSite (B:=B) out offset m pos bmap hmap gmap nmap reg (fun u => ⟨atSite,u⟩) block host group slot)
    (reached : history → Palette.readsAtView dict enc sh reg) : rangeAtSite dict enc sh atSite history out offset m pos bmap hmap gmap nmap reg block host group slot := by
  intro copies stored pitch cap u rotor fit sp seen j f
  exact (raw stored pitch cap u (j.castLE fit) f (sp f (j.castLE fit)) (seen _ _)).trans
    (reached copies atSite u rotor j f)

section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "unitCost_" => q₀*(wire₀:ℝ)
local notation "depthBound_" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "pinSizes_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "widthDiv_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
private def branchRegister {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) : Prop :=
  ∀ (pages : RangePages b.origin.source hp b.origin.archive) (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    (age : 0 < S.height) (hostDim : S.hostSize S.length = out.receiver.hosts) (groupDim : S.groupCount S.length = out.receiver.groups)
    (nodeDim : S.epochPower^S.localTokenExponent = out.nodes) (blockDim : 2^k = out.receiver.blocks),
    sameRegister (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit) out offset m pos
      (fun x => ((Reached.NodeCells.coordinate b.target x.1).2.2).cast blockDim)
      (fun x => ((Reached.NodeCells.coordinate b.target x.1).1).cast hostDim)
      (fun x => ((Reached.NodeCells.coordinate b.target x.1).2.1).cast groupDim)
      (fun x => (((Branch.localNodes X G S (r:=r) (c:=c) b hp x.1 x.2).castLE (Branch.site_nodes X G S (r:=r) (c:=c) b hp age x.1)).cast nodeDim))
      (pages b.path (b.path.recorded_whole p b.recorded))

private theorem branchRegisterHolds {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) : branchRegister X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp := by
  intro pages out w offset m pos age hostDim groupDim nodeDim blockDim
  apply sameRegisterHolds
private def branchRaw {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (tail : ℕ) : Prop :=
  ∀ (pages : RangePages b.origin.source hp b.origin.archive) (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    {half rest : ℕ} (base : S.baseGroups = 2^tail) (width : S.groupWidth k tail 0+k = half+(half+rest))
    (age : 0 < S.height) (hostDim : S.hostSize S.length = out.receiver.hosts) (groupDim : S.groupCount S.length = out.receiver.groups)
    (nodeDim : S.epochPower^S.localTokenExponent = out.nodes) (blockDim : 2^k = out.receiver.blocks),
    let order := Branch.leafOrder X G S (r:=r) (c:=c) b hp base width
    let nums := Branch.localNodes X G S (r:=r) (c:=c) b hp
    let coord := Reached.NodeCells.coordinate b.target
    ∀ (i : Fin (S.hostSize S.length)) (z : Fin (order.site i).nodes),
    let vertex := order.node i z
    rawAtSite (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit) out offset m pos
       (fun x => ((coord x.1).2.2).cast blockDim) (fun x => ((coord x.1).1).cast hostDim)
       (fun x => ((coord x.1).2.1).cast groupDim)
       (fun x => (((nums x.1 x.2).castLE (Branch.site_nodes X G S (r:=r) (c:=c) b hp age x.1)).cast nodeDim))
       (pages b.path (b.path.recorded_whole p b.recorded)) (fun u => ⟨vertex,u⟩)
       ((b.target.placement.block vertex).cast blockDim) (i.cast hostDim) (((b.target.placement.pos vertex).1).cast groupDim)
       (fun u => ((DescentTerminalChronologicalBooks.ordinal ((nums vertex).toEmbedding.trans Fin.valEmbedding) u).castLE
            (Branch.site_nodes X G S (r:=r) (c:=c) b hp age vertex)).cast nodeDim)

private theorem branchRawHolds {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (tail : ℕ) : branchRaw X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp tail := by
  intro pages out w offset m pos half rest base width age hostDim groupDim nodeDim blockDim order nums coord i z vertex
  apply rawAtSiteHolds
  · intro u; rfl
  · intro u
    exact congrArg (fun h : Fin (S.hostSize S.length) => h.cast hostDim)
      ((((Branch.leafOrder X G S (r:=r) (c:=c) b hp base width).nodes i).symm z).property)
  · intro u; rfl
  · intro u
    exact Fin.ext (ordinal_equiv_value _ u).symm
private def branchRangeAtSite {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op) (tail : ℕ) : Prop :=
  ∀ (pages : RangePages b.origin.source hp b.origin.archive) (out : ResetOutput) {w : ℕ} (offset : ℕ) (m : Memory w) (pos : 0 < out.receiver.lanes)
    {half rest : ℕ} (base : S.baseGroups = 2^tail) (width : S.groupWidth k tail 0+k = half+(half+rest))
    (age : 0 < S.height) (hostDim : S.hostSize S.length = out.receiver.hosts) (groupDim : S.groupCount S.length = out.receiver.groups)
    (nodeDim : S.epochPower^S.localTokenExponent = out.nodes) (blockDim : 2^k = out.receiver.blocks),
    let order := Branch.leafOrder X G S (r:=r) (c:=c) b hp base width
    let nums := Branch.localNodes X G S (r:=r) (c:=c) b hp
    let coord := Reached.NodeCells.coordinate b.target
    ∀ (i : Fin (S.hostSize S.length)) (z : Fin (order.site i).nodes),
    let vertex := order.node i z
    let code := encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) fixed b.origin.archive (Palette.encodedOrigin (p:=p) b.origin op menu)
    rangeAtSite (G:=G) (s:=s₀) (Z:=S.grainAt G.b p 0) (p:=p) («R»:=R) (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit)
       (dictionary (s:=s₀) (Z:=S.grainAt G.b p 0) G op menu p) code (Branch.bundleShape X G S (r:=r) (c:=c) b hp stride) vertex
       (Copies hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
         b.path (b.path.recorded_whole p b.recorded) b.aligned) out offset m pos
       (fun x => ((coord x.1).2.2).cast blockDim) (fun x => ((coord x.1).1).cast hostDim)
       (fun x => ((coord x.1).2.1).cast groupDim)
       (fun x => (((nums x.1 x.2).castLE (Branch.site_nodes X G S (r:=r) (c:=c) b hp age x.1)).cast nodeDim))
       (pages b.path (b.path.recorded_whole p b.recorded))
       ((b.target.placement.block vertex).cast blockDim) (i.cast hostDim) (((b.target.placement.pos vertex).1).cast groupDim)
       (fun u => ((DescentTerminalChronologicalBooks.ordinal ((nums vertex).toEmbedding.trans Fin.valEmbedding) u).castLE
            (Branch.site_nodes X G S (r:=r) (c:=c) b hp age vertex)).cast nodeDim)

private theorem branchRangeAtSiteHolds {he : 0≤ε₀} {hu : 0≤unitCost_} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op) (tail : ℕ) : branchRangeAtSite X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed tail := by
  intro pages out w offset m pos half rest base width age hostDim groupDim nodeDim blockDim order nums coord i z vertex code
  apply rangeAtSiteHolds
  · exact branchRawHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp tail pages out offset m pos base width age hostDim groupDim nodeDim blockDim i z
  · exact Palette.branchReadsOfHistory X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed pages
end

variable {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
attribute [local irreducible] branchRegister branchRaw branchRangeAtSite Palette.selectedBranch

/-- Pointwise equality of the four measured finite addresses fixes the decoded register. -/
theorem normalized_range_register (c : (last).Choice) :
    branchRegister X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive :=
  branchRegisterHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive

theorem normalized_raw_range_word (c : (last).Choice) :
    branchRaw X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive tail :=
  branchRawHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive tail

theorem normalized_range_reads (c : (last).Choice) :
    branchRangeAtSite X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive (Nat.le_max_left 1 (max reset.bitsR (C * reset.bitsR))) (RotorSpec.ofRates reset) reset.menu
      (Palette.selectedRotor X G S ordinary reset branch positive room shorten c) tail :=
  branchRangeAtSiteHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=W*piece)
      (r:=(cert).choose) (c:=c) (Palette.selectedBranch X G S ordinary reset branch positive room shorten c) positive (Nat.le_max_left 1 (max reset.bitsR (C * reset.bitsR))) (RotorSpec.ofRates reset) reset.menu
      (Palette.selectedRotor X G S ordinary reset branch positive room shorten c) tail

end
end Hierarchy.DescentSixParty.SeedNamed

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentColonies DescentInitialHost
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentPackedSeed DescentMixedRouter DescentResetInvoice DescentTerminalSliceRuns DescentTerminalCombinedRole
open DescentRetainedRangeDigits DescentDatedAddressBook DescentDatedPriorOperand
open DescentSIMDLookup DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false

open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
attribute [local irreducible] Origin.source Origin.archivePackage Branch.bundleShape Branch.localNodes
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "s" => S.firstWidth G.b p
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c
local notation "whole_" => (b).path.recorded_whole p (b).recorded
local notation "one_" => (le_max_left 1 (max reset.bitsR (C*reset.bitsR)))
local notation "pinDiv" => (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b)
local notation "pins_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "shape_" => Origin.archiveShape (b).origin p R positive one_ pinDiv
variable (pages : RangePages (issued X G S ordinary reset branch positive room shorten c).origin.source positive
  (issued X G S ordinary reset branch positive room shorten c).origin.archive)
variable (out : ResetOutput) {w : ℕ} (offset : ℕ) (mem : Memory w) (pos : 0<out.receiver.lanes)
variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
    (age : 0<S.height)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "bits_" => (Branch.archive X G S b positive).bit
local notation "order_" => Branch.localNodes X G S b positive
local notation "coord_" a:arg => Reached.NodeCells.coordinate (b).target a
local notation "nodeCap" => S.epochPower^S.localTokenExponent
variable (hostDim : S.hostSize S.length=out.receiver.hosts) (groupDim : S.groupCount S.length=out.receiver.groups)
    (nodeDim : S.epochPower^S.localTokenExponent=out.nodes) (blockDim : 2^k=out.receiver.blocks)
local notation "blocks_" => fun x : NodeOrder.All bits_=>((coord_ x.1).2.2).cast blockDim
local notation "hosts_" => fun x : NodeOrder.All bits_=>((coord_ x.1).1).cast hostDim
local notation "groups_" => fun x : NodeOrder.All bits_=>((coord_ x.1).2.1).cast groupDim
local notation "nums_" => fun x : NodeOrder.All bits_=>
  (((order_ x.1 x.2).castLE (Branch.site_nodes X G S b positive age x.1)).cast nodeDim)
local notation "actual" => fromRAM (PriorResetArchive.reset out offset) out.rangeLayout out.nodeBits mem pos
  blocks_ hosts_ groups_ nums_
variable (i : Fin (S.hostSize S.length)) (z : Fin ((Branch.leafOrder X G S (issued X G S ordinary reset branch positive room shorten c) positive base width).site i).nodes)
local notation "v" => (ord).node i z
local notation "place" => (b).target.placement
local notation "g_" => ((place).pos v).1
local notation "block_" => (place).block v
local notation "birth_" => (order_ v).toEmbedding.trans Fin.valEmbedding
local notation "slot_" u:arg => (DescentTerminalChronologicalBooks.ordinal birth_ u).castLE
  (Branch.site_nodes X G S b positive age v)
local notation "spans_" u:arg => repeatFields (((sh).sites v).sliceFields u).flatten

open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentTerminalSliceRuns DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open DescentTerminalPointerDigits DescentOperandStateBanks
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "M" => out.argumentSlots
local notation "a₀" => max 8 (2^S.capGain)
local notation "colors_" => DescentPrimitivePalette.colors G s Z rot
local notation "dict" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "fieldBits" => DescentTerminalCombinedRole.width colors_ a₀ cap p R
local notation "L" => Columns M
local notation "slices" y_:arg a_:arg => ((sh).sites y_).sliceFields a_
local notation "headers" y_:arg a_:arg => repeatFields (slices y_ a_).flatten


variable {d : ℕ} (start advice : ℕ) (cfg : RawWidths) (original acquired : Memory w)
local notation "sites_" => S.hostSize S.length
local notation "cohorts_" => S.groupCount S.length
local notation "rows_" => 2^k*sites_
variable (cables : Fin (Columns out.argumentSlots)→Fin (2^k)→Gather.Address)
local notation "sizes_" => fun f : Fin 6 => fieldBits f*nodeCap*cohorts_
local notation "columns_" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows_ f.val
local notation "table_" => DescentTerminalRoleTables.role sizes_ columns_ advice
local notation "printer" => writePanel (d:=d) («M»:=M) («s»:=s) («Z»:=Z) (N:=nodeCap) (groups:=cohorts_) G rot a₀ cap p R cfg
local notation "out_" => DescentTerminalSliceShelf.memory start cables printer sites_ original
local notation "end_" => DescentTerminalSliceShelf.fence start L d rows_
local notation "rawAt" => DescentTerminalSliceShelf.seen (d:=d) cables original block_ i
local notation "input_" u:arg => extract cfg rawAt g_ (slot_ u)
local notation "fetched" => observed (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R)
  (N:=nodeCap) («M»:=cohorts_) table_ acquired ((finProdFinEquiv (block_,i)).val:Computability.VPVNP.BurstRAM.Word w)


/-- The original registered events supply all three rotor header digits observed by the printed role. -/
theorem normalized_registered_role (u : ((palette).recipe v).Node)
    (ok : ∀ field block,(cables field block).Fits start sites_ w) (off : 2^d<2^w)
    (room_ : end_<2^w) (fitsWord : ∀ f,sizes_ f≤w)
    (kept : ∀ j<end_,acquired j=out_ j)
    (fit : (headers v u).length≤M)
    (T : Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.primitive.chart.bits*out.nodes))
    (Q : Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.nodeBits*out.nodes))
    (sp : Fin 3→Fin M→Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.nodeBits*out.nodes))
    (decoded : Decoded out (i.cast hostDim) ((g_).cast groupDim) ((slot_ u).cast nodeDim) T Q sp (input_ u))
    (token : ((encode out.primitive.chart.bits out.nodes).symm
      (T (i.cast hostDim) ((g_).cast groupDim)) ((slot_ u).cast nodeDim)).val=
        ((dict).store (((palette).recipe v).tag u)).val+1)
    (count : ((encode out.nodeBits out.nodes).symm
      (Q (i.cast hostDim) ((g_).cast groupDim)) ((slot_ u).cast nodeDim)).val=
        (((sh).sites v).recipe positive).arity u)
    (ordinaryEvent : ∀a (e : (b).path.Event a),e.isReset=false →
      rangeAtEvent positive (b).origin.archive pages one_ pins_ shape_ (b).path e)
    (resetEvent : ∀a (e : (b).path.Event a),e.isReset=true →
      rangeAtEvent positive (b).origin.archive pages one_ pins_ shape_ (b).path e)
    (registers : pages (b).path whole_=actual)
    (pitch : out.receiver.lanes=out.receiver.groups) (word : out.nodeBits*out.nodes*out.receiver.lanes≤w)
    (seen : ∀j f,Reads (out.terminalField offset (page f) j ((block_).cast blockDim))
      (sp f j) out.receiver.groups mem) :
    Printed dict (DescentTerminalCombinedRole.fields (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) (node (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) fetched g_ (slot_ u))) (((palette).recipe v).tag u) (slices v u) :=by
  have copied := (range_history positive (b).origin.archive pages one_ pins_ shape_ (b).path whole_
    (b).aligned ordinaryEvent resetEvent).1
  apply normalized_previous_decoded X G S ordinary reset branch positive room shorten c out start advice cfg
    original acquired base width age cables i z u ok off room_ fitsWord kept fit hostDim groupDim nodeDim T Q sp decoded token count
  intro rotor j f
  exact normalized_range_reads X G S ordinary reset branch positive room shorten c pages out offset
    mem pos base width age hostDim groupDim nodeDim blockDim i z copied registers pitch word u rotor fit sp seen j f

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
