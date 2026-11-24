import OAI.Computability.VPVNP.PairShrinkRoleSelectedChildren
import OAI.Computability.VPVNP.PairShrinkRoleParsed
import OAI.Computability.VPVNP.PairShrinkRolePhysicalHidden
import OAI.Computability.VPVNP.PairShrinkRoleSiteOperands
import OAI.Computability.VPVNP.PairShrinkCallFrameStores

/-!
# Exact native parser at a selected shrinking site

The level switch, argument directory, two field readers and resident-map header
are all linked to the installed image. Their outputs are the actual map operands
and the ordered private stores, starting at the caller's original scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords LocalHistory
open NodeArguments NodeArguments.ChildScan TraversalRows TraversalRoles TraversalControllerInputs
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentInputs MapResidentRows
open ShrinkHiddenGuess
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t : ℕ} (ord : B.Entry → Fin t) {w p r n : ℕ} (M : Machine w p r 11)
  (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
  (installed : ∀ k, M.code (pc k) = ((shrinkSegment B ord).row pc dfs saved reg done k).resize w)
  (separate : ∀ k : Fin 9, k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7 → ∀ l, dfs k ≠ reg l)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "lr" => LocatedBody.commonLocator (active B ord) reg

variable {H first pitch offset base : ℕ} {raw m : Memory w}
  (ds : (j : Fin (executeLevels B f hf T hT X z).length) →
    LevelDirectory (executeLevels B f hf T hT X z)[j] raw base)
  (resident : Resident M.publicData m H first pitch offset B.recordLimit base
    ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))
  (j : Fin (executeLevels B f hf T hT X z).length)
  (id : Fin (executeLevels B f hf T hT X z)[j].outputSites)
  (shrinking : tagLevel B f hf (executeLevels B f hf T hT X z)[j] = .shrink) (i : Fin S.steps)
  (index : (executeLevels B f hf T hT X z)[j].origin.ordinal = i.val)
  (fit : layerBase B.recordLimit base (TraversalRoles.selected B f hf T hT X z)
    ((executeLevels B f hf T hT X z).length + 1) < 2 ^ w)
  {g : ℕ} (Z : State (oldExponent i) (packingLaneBits (oldExponent i) g))
  (regions : LeafArena.Regions) (inc : IncidenceDirectory w) (older : ℕ)
  (desc : Word w → ChildArguments.Descriptor w Z) (rep : inc.ActualColumns Z m)
  (strideFit : B.recordLimit + 2 < 2 ^ w)

local notation "level" => levelHead M.publicData m j.val
local notation "targetAddr" => address B.recordLimit (layerBase B.recordLimit base tags (j.val + 1))
  id.val
local notation "arena" => LeafArena.Regions.arguments regions
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "cs" => selectedChildSetup M.publicData m (List.length passes) j.val S.steps i.val
  (oldExponent i)
local notation "hs" => physicalHiddenSetup B.shrink.selectorBits (hiddenStride i) (Fin.val level) m
local notation "common" => shared B ord i reg
local notation "P" => mapLoop B ord i pc reg done

private noncomputable abbrev originalRows (xs : List (Child Z)) :=
  xs.map (Child.packet Z older B.recordLimit)

local notation "packets" => originalRows B i Z older

variable (arg : Args w) (seed : List ShrinkHiddenGuess.Row) (sel : Z.ShrinkSelection B.shrink)
  (side : Bool) (site : MapResidentRows.Site Z) (term : Word w)
  (source : MapRowSource Z sel side m (levelHead M.publicData m j.val) term)
  (ready : DFS.Scratch w n → Prop)
  (actions : List (Child Z) → List ShrinkHiddenGuess.Row → List (ResidentMapLoop.Exact.Action w n))
  (inv : List (Child Z) → List ShrinkHiddenGuess.Row → Word w → Config w p r → Prop)

local notation "ms" => mapStartSetup m level (Fin.val (siteIndex Z site) : Word w)
local notation "src" => firstMap B i source site

set_option maxHeartbeats 4000000 in
-- Align each selected stage and its nested finite code and register embeddings.
include installed separate ds resident shrinking index fit rep strideFit in
/-- The original DFS hook executes all local readers on an arbitrary tape, including
truncated arguments and rejections inside the resident row. -/
theorem physicalSite_exactOn
    (frame : ∀ priv, ready (DFS.scratch n priv) → ShrinkCallFrameLive.Stored regions n priv)
    (above : n ≤ NativeFrame.frameBase regions)
    (frameRoom : NativeFrame.frameBase regions + 12 ≤ 2 ^ w)
    (directory : ∀ node : Word w, node.val = targetAddr →
      (desc node).directoryBase = level + 14 ∧
      ChildArguments.Resident arena inc m older B.recordLimit n node (desc node))
    (bounds : ∀ node : Word w, node.val = targetAddr → ∀ u ∈ (desc node).sites,
      childNode Z older B.recordLimit u < regions.nodes ∧
        n < (arena).base (childNode Z older B.recordLimit u))
    (selectors : arg.selectorBits = (B.shrink.selectorBits : Word w))
    (rowStride : arg.rowStride = hiddenStride i) (headRoom : (level).val + 38 < 2 ^ w)
    (headers : ShrinkHiddenGuess.Header.Published arg (level).val m)
    (countFit : arg.countBase + arg.owner < 2 ^ w)
    (count : (m (arg.countBase + arg.owner)).val = seed.length)
    (valid : ValidRows arg m seed) (baseWord : arg.scratchBase = heap)
    (pitchWord : arg.slotStride = n * n) (ownerWord : arg.owner = id.val)
    (siteWord : (siteIndex Z site).val = id.val)
    (words : MapResidentInputs.Published m level
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 3)
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 5) term 10)
    (lengths : ∀ xs es, (actions xs es).length = (order Z side site).length)
    (initial : ∀ node (priv : Word w → Word w) xs es c, node.val = targetAddr →
      ready (DFS.scratch n priv) → xs.map Child.site = (desc node).sites → ValidRows arg m es →
      Parsed (n := n) (hiddenReader arg m seed) node es →
      SiteMapInput common dfs regions n node level term
        (storeRows arg.scratchBase arg.slotStride es (storePackets arena (packets xs) priv)) c →
      inv xs es node c)
    (stable : ∀ xs es node, (P).Stable (inv xs es node))
    (items : ∀ xs es, ResidentMapLoop.Exact.Items P M m dfs (inv xs es) src (actions xs es))
    (mapRoom : src + (order Z side site).length < 2 ^ w) :
    (hook (visitReader arena inc m older B.recordLimit desc (fun _ => arg) (fun _ => seed) actions
      cs (fun _ => hs) (fun _ _ => ms))).ExactOn (fun node s => node.val = targetAddr ∧ ready s)
      M (pc (shrinkSegment B ord).entry) done dfs m := by
  let pre (node : Word w) (c : Config w p r) :=
    c.pc = pc (shrinkSegment B ord).entry ∧ c.reg (dfs 7) = node ∧ node.val = targetAddr ∧
    c.reg (dfs 6) = (n : Word w) ∧ ready (DFS.scratch n c.privateMem)
  let argsEnd (xs : List (Child Z)) (node : Word w) (d : Config w p r) :=
    d.pc = afterChildPC B ord i pc (afterChildren B ord i).code.entry ∧
    VertexLevel.Located M.publicData m lr node j.val (id.val : Word w) d ∧
    d.reg (dfs 6) = (n : Word w) ∧ ShrinkCallFrameLive.Stored regions n d.privateMem ∧
    node.val = targetAddr ∧ xs.map Child.site = (desc node).sites ∧
    ∃ priv, ready (DFS.scratch n priv) ∧ d.privateMem = storePackets arena (packets xs) priv
  have children : Realizes (endAddr := n) (bind (cs).reader fun _ =>
      ChildArguments.reader arena inc m older B.recordLimit desc) M m dfs pre argsEnd := by
    apply selectedChildren_realizes B ord M pc dfs saved reg done f hf T hT X z installed ds
      resident j id shrinking i index fit separate Z arena inc older desc rep strideFit
      (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) (fun node _ h => directory node h.2.2.1)
    intro node c d xs hc sites ep loc endEq _ mem
    have addr := hc.2.2.1
    have row := (directory node addr).2
    have child (x : Child Z) (hx : x ∈ xs) := bounds node addr x.site
      (sites ▸ List.mem_map_of_mem hx)
    have fs : ∀ q ∈ packets xs, q.Fits arena w n := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      have hx' : x.site ∈ (desc node).sites := sites ▸ List.mem_map_of_mem hx
      exact ⟨row.stack _ hx', (Child.payload_length Z x) ▸ row.stride _ hx',
        (Child.payload_length Z x) ▸ (row.room _ hx').le⟩
    have geom := (frame _ hc.2.2.2.2).children (packets xs) fs
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq; exact (child x hx).1)
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq; exact (child x hx).2) frameRoom
    exact ⟨ep,loc,endEq.trans hc.2.2.2.1,mem ▸ geom,addr,sites,c.privateMem,hc.2.2.2.2,mem⟩
  let hiddenEnd (xs : List (Child Z)) (es : List ShrinkHiddenGuess.Row) (node : Word w)
      (d : Config w p r) :=
    d.pc = reloadStart B ord i pc ∧ d.reg (lr 0) = node ∧ d.reg (lr 11) = level ∧
    d.reg (lr 7) = (id.val : Word w) ∧ d.reg (lr 8) = (heap : Word w) ∧
    d.reg (dfs 6) = (n : Word w) ∧ ShrinkCallFrameLive.Stored regions n d.privateMem ∧
    node.val = targetAddr ∧ xs.map Child.site = (desc node).sites ∧ ValidRows arg m es ∧
    ∃ priv, ready (DFS.scratch n priv) ∧ d.privateMem =
      storeRows arg.scratchBase arg.slotStride es (storePackets arena (packets xs) priv)
  have hidden (xs) : Realizes (endAddr := n) (bind (hs).reader fun _ => hiddenReader arg m seed)
      M m dfs (argsEnd xs) (hiddenEnd xs) := by
    apply physicalHidden_realizes B ord i M pc dfs saved reg done installed separate m arg
      (level).val selectors rowStride headRoom headers
    · intro node d hd
      obtain ⟨ep, loc, endWord, geom, _⟩ := hd
      refine ⟨ep, ownerWord ▸ loc.owner, loc.oldHead.trans (Fin.cast_val_eq_self _).symm, ?_, ?_⟩
      · dsimp only
        rw [endWord, geom.pointer, geom.cache, geom.length, VertexLevel.hiddenBaseWord_cast,
          baseWord]
        rfl
      · dsimp only
        rw [endWord, geom.pointer, geom.length, pitchWord, Nat.cast_mul]
    · exact countFit
    · exact count
    · exact valid
    · rw [baseWord]
      exact above.trans (by
        unfold NativeFrame.frameBase ShrinkCallABI.hiddenBase LeafArena.Regions.stackBase
          LeafArena.Regions.cacheBase
        omega)
    · intro node c d es hc validRows ep mem _ cache locs ext
      obtain ⟨_, loc, endWord, geom, addr, sites, priv, good, childMem⟩ := hc
      have hf (e) (he : e ∈ es) : heap + e.1 * arg.slotStride + e.2.length ≤ 2 ^ w := by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
        simpa only [← baseWord, Args.slot] using (validRows ⟨k, hk⟩).2.2.le
      have gg := geom.hidden arg.slotStride es above hf
      rw [← baseWord] at gg
      have df : d.reg (dfs 6) = c.reg (dfs 6) := ext _
        (separate 6 (by decide) _) (fun ⟨_, eqn⟩ => separate 6 (by decide) _ eqn.symm)
      exact ⟨ep, (locs 0 (by decide)).trans loc.state.node,
        (locs 11 (by decide)).trans loc.oldHead, (locs 7 (by decide)).trans loc.owner,
        baseWord ▸ cache, df.trans endWord, mem ▸ gg, addr, sites, validRows, priv, good,
        childMem ▸ mem⟩
  have commonApart (k : Fin 9) (hk : k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) :
      dfs k ∉ Set.range common := fun ⟨_, h⟩ => separate k hk _ h.symm
  have ownerFit : id.val < 2 ^ w := by rw [← ownerWord]; omega
  have load (xs es) : Realizes (endAddr := n) (ms).reader M m dfs
      (fun node c => hiddenEnd xs es node c ∧
        Parsed (n := n) (bind (hs).reader (fun _ => hiddenReader arg m seed)) node es)
      (fun _ => ResidentMapLoop.Exact.Entry P (inv xs es) src (actions xs es).length) := by
    rw [lengths]
    apply mapStart_realizes B ord i pc reg done source site M dfs saved installed words
      (by omega) (fun _ _ h => h.1.1)
    · intro node c hc
      exact (congrArg c.reg (map_locator_shared B ord i reg 11)).trans hc.1.2.2.1
    · intro node c hc
      have eqn := (congrArg c.reg (map_locator_shared B ord i reg 7)).trans hc.1.2.2.2.1
      exact (congrArg Fin.val eqn).trans ((Nat.mod_eq_of_lt ownerFit).trans siteWord.symm)
    · exact commonApart
    · intro node c d input start
      obtain ⟨hc, parsed⟩ := input
      obtain ⟨_, atNode, atLevel, _, cache, endWord, geom, addr, sites, validRows, priv, good, mem⟩
        := hc
      exact initial node priv xs es d addr good sites validRows parsed.afterSetup
        (siteMapInput_of_start B ord i reg dfs regions (separate 6 (by decide)) geom endWord atNode
          atLevel cache mem start)
  have link := (map_linked B ord i M (matrixPC B ord i pc) dfs saved (reloadRegs B ord i reg)
    done (selected_map_rows B ord i M pc dfs saved reg done installed)).loop
  have endLabel : (P).done = done := rfl
  have loops xs es : Realizes (ResidentMapLoop.Exact.mapReader (actions xs es)) M m dfs
      (ResidentMapLoop.Exact.Entry P (inv xs es) src (actions xs es).length)
      (fun _ _ d => d.pc = done) := (ResidentMapLoop.Exact.maps_realizes P link (stable xs es)
    (fun k hk => separate k hk _) (actions xs es) src (items xs es)
    ((lengths xs es) ▸ mapRoom)).weakenPost (fun _ _ _ h => h.1.trans endLabel)
  have run := children.bind fun xs => (hidden xs).withParsed.bind fun es =>
    (load xs es).bind fun _ => loops xs es
  have path : Realizes (visitReader arena inc m older B.recordLimit desc (fun _ => arg)
      (fun _ => seed) actions cs (fun _ => hs) (fun _ _ => ms)) M m dfs pre
      (fun _ _ d => d.pc = done) := by
    simpa only [visitReader, bind_assoc] using run
  apply path.exactOn _ (fun node c _ _ h entry =>
    ⟨entry.pc, entry.nodeWord, h.1, entry.endWord, h.2⟩)
  intro node s bs out rest _ h
  have sc : Splits (endAddr := n) (ChildArguments.reader arena inc m older B.recordLimit desc) :=
    fun _ _ _ _ _ h => ChildArguments.splitBits arena inc m older B.recordLimit desc h
  have sh : Splits (endAddr := n) (hiddenReader arg m seed) := hiddenReader_split arg m seed
  have quiet xs es : Splits (ResidentMapLoop.Exact.mapReader (actions xs es)) :=
    fun _ _ _ _ _ h => ResidentMapLoop.Exact.splitBits (items xs es |>.quiet) h
  exact ((cs).splits.bind fun _ => sc.bind fun xs => (hs).splits.bind fun _ =>
    sh.bind fun es => (ms).splits.bind fun _ => quiet xs es)
    node s bs out rest h

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
