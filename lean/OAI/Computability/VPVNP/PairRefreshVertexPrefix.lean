import OAI.Computability.VPVNP.PairRefreshVertexAssembly
import OAI.Computability.VPVNP.PairRefreshVertexPacket
import OAI.Computability.VPVNP.PairVertexStageRun
import OAI.Computability.VPVNP.PairVertexStageChildren

/-!
# Locating and decoding the unique child at a refresh visit

The raw DFS node selects a level header. The actual child directory and singleton
preimage row supply the address of the older node. A complete guess stores its
half-wire values in that node's frame and reaches the refresh kernel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshVertexAssembly

open BurstRAM BurstRAM.PrivateRAM VertexImage VertexStagePrefix NodeArguments NodeArguments.ChildScan
open TraversalControllerInputs TraversalRoles TraversalRows Compression CompressorRecords
open scoped Fin.CommRing

variable {w p r g : ℕ} (a : ℕ) (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs)
  (loc : Fin (segment a body locator).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (segment a body locator).privateRegs ↪ Fin r) (done : Fin p) (M : Machine w p r 11)
  (installed : Installed a body locator loc dfs saved reg done M)
  (X : State a g) (site : X.network.Site) (old : X.network.Half site)
  (U : IncidenceDirectory w) (m : Memory w) (A : Arena) (older cap listHead : ℕ)

local notation "child" => childNode X older cap site
local notation "half" => Child.ofHalf X site old
local notation "packet" => Child.packet X older cap half
local notation "args" => packed X site old
local notation "bank" => levelRegs a body locator reg
local notation "P₀" => childPreparation a body locator
local notation "cp" => childPC a body locator loc

/-- Input-stage trace through level location, register handoff, child-header reads, and the
scan of the single old half-wire packet. -/
noncomputable def inputTrace (pub : Fin 11 → Word w) (node : Word w) (level later : ℕ) :=
  VertexLevel.trace pub m (level+1) later ++
    (List.replicate 2 (.tick : Event w) ++
      (List.replicate (2^a) (.tick : Event w) ++
        (ChildHeader.events m node (levelHead pub m level+14) ++ ChildScan.events X U m listHead [half])))

/-- Exact work and external probes before entry to the resident map. Only the
older half-wire packet is taken from the branch bitstream. -/
theorem inputTrace_cost (pub : Fin 11 → Word w) (node : Word w) (level later : ℕ) :
    let es := inputTrace a X site old U m listHead pub node level later
    es.length = 63 + 6*later + 16*2^a + 6*(args).length ∧
      countProbes es = 15 + later + 3*2^a ∧ choiceBits es = args := by
  intro es
  obtain ⟨ll,lp,lc⟩ := VertexLevel.trace_cost pub m (level+1) later
  obtain ⟨hp,hl,hc⟩ := ChildHeader.cost m node (levelHead pub m level+14)
  obtain ⟨cc,cp',cl⟩ := events_cost X U m listHead [half]
  simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    Child.payload_ofHalf] at cc cp' cl
  have tick (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 ∧
      choiceBits (List.replicate n (.tick : Event w)) = [] := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih => simpa only [List.replicate_succ,countProbes,choiceBits] using ih
  simp only [es,inputTrace,List.length_append,List.length_replicate,countProbes_append,
    PrimedInputRAM.Flow.choiceBits_append,(tick _).1,(tick _).2,lc,hc,cc,cp',lp,hp,hl,ll,cl,List.nil_append]
  constructor
  · omega
  · exact ⟨by omega, trivial⟩

include installed in
/-- Reach the selected refresh body with its locator intact and with all of the
guessed child fields installed in the older node's own private memory. -/
theorem load_child {header first pitch offset base : ℕ} {initial : TaggedLayer} {ls : List (Fiber w)}
    (heads : Resident M.publicData m header first pitch offset cap base initial ls)
    (j : Fin (initial :: ls.map Prod.fst).length) (level : ℕ) (hj : j.val = level+1)
    (id : Fin (initial :: ls.map Prod.fst)[j].layer.count) (c : Config w p r)
    (entry : c.pc = loc (segment a body locator).entry)
    (node : (c.reg (dfs 7)).val = address cap (layerBase cap base (initial :: ls.map Prod.fst) j) id)
    (endFit : layerBase cap base (initial :: ls.map Prod.fst) (ls.length+1) < 2^w)
    (fields : (directory a older cap A U).Stored m (levelHead M.publicData m level + 14))
    (row : DFS.Row m (c.reg (dfs 7)).val listHead [(child : Word w)])
    (rep : U.ActualColumns X m) (strideFit : cap+2 < 2^w)
    (nodeFit : child < 2^w) (packetFit : A.base child+(args).length < 2^w) :
    ∃ out, ChildScan.Prefix M m c out args
      (inputTrace a X site old U m listHead M.publicData (c.reg (dfs 7)) level (ls.length-(level+1))) ∧
      out.pc = bodyPC a body locator loc body.entry ∧
      VertexLevel.Located M.publicData m bank (c.reg (dfs 7)) level (id.val : Word w) out ∧
      out.privateMem = storePackets A [packet] c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ q, q ∉ Set.range reg → out.reg q = c.reg q := by
  obtain ⟨mid,first,atChild,located,frame⟩ := locate a body locator loc dfs saved reg done M installed
    heads j level hj id c entry node endFit
  have row' : DFS.Row m (mid.reg (bank 0)).val listHead
      ([half].map fun q => (childNode X older cap q.site : Word w)) := located.state.node.symm ▸ row
  have node' : ∀ q ∈ [half], childNode X older cap q.site < 2^w := by
    intro q h; exact List.mem_singleton.mp h ▸ nodeFit
  have fit' : ∀ q ∈ [half], A.base (childNode X older cap q.site) + (q.payload X).length < 2^w := by
    intro q h; rw [List.mem_singleton.mp h,Child.payload_ofHalf]; exact packetFit
  obtain ⟨out,ep,pers,mem,_,kept,scan⟩ := VertexStagePrefix.child_run body locator M cp dfs saved reg done
    (linked a body locator loc dfs saved reg done M installed).2 rep [half] listHead mid atChild
    (located.oldFields.symm ▸ fields) row' strideFit node' fit'
  have nodeWord : mid.reg (locatorRegs body locator reg 0) = c.reg (dfs 7) := located.state.node
  have dirWord : mid.reg (locatorRegs body locator reg 12) = levelHead M.publicData m level+14 := located.oldFields
  have bodyPath : ChildScan.Prefix M m mid out args (List.replicate 2 .tick ++ (List.replicate (2^a) .tick ++
      (ChildHeader.events m (c.reg (dfs 7)) (levelHead M.publicData m level+14) ++ ChildScan.events X U m listHead [half]))) := by
    simpa only [List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,Child.packet,
      Child.payload_ofHalf,nodeWord,dirWord] using scan
  refine ⟨out,first.trans bodyPath,ep,?_,?_,pers.trans frame.persistent,?_⟩
  · apply VertexStageDispatch.retainLocated located
    intro i
    exact kept _ (fun ⟨j,eqn⟩ => Preparation.disjoint reg j (locator i) eqn)
  · rw [mem,frame.privateMem]; rfl
  · intro q hq
    exact (kept q (fun ⟨_,eqn⟩ => hq ⟨_,eqn⟩)).trans (frame.outside q (fun ⟨_,eqn⟩ => hq ⟨_,eqn⟩))


include installed in
/-- A truncated packet rejects in the actual child stage, independently of the continuation. -/
theorem reject_short {header first pitch offset base : ℕ} {initial : TaggedLayer} {ls : List (Fiber w)}
    (heads : Resident M.publicData m header first pitch offset cap base initial ls)
    (j : Fin (initial :: ls.map Prod.fst).length) (level : ℕ) (hj : j.val = level+1)
    (id : Fin (initial :: ls.map Prod.fst)[j].layer.count) (c : Config w p r)
    (entry : c.pc = loc (segment a body locator).entry)
    (node : (c.reg (dfs 7)).val = address cap (layerBase cap base (initial :: ls.map Prod.fst) j) id)
    (endFit : layerBase cap base (initial :: ls.map Prod.fst) (ls.length+1) < 2^w)
    (fields : (directory a older cap A U).Stored m (levelHead M.publicData m level + 14))
    (row : DFS.Row m (c.reg (dfs 7)).val listHead [(child : Word w)])
    (rep : U.ActualColumns X m) (strideFit : cap+2 < 2^w)
    (nodeFit : child < 2^w) (packetFit : A.base child+(args).length < 2^w)
    (bs : List Bool) (short : bs.length < (args).length) : ¬ DFS.Returns M c m bs := by
  obtain ⟨mid,first,atChild,located,_⟩ := locate a body locator loc dfs saved reg done M installed
    heads j level hj id c entry node endFit
  have row' : DFS.Row m (mid.reg (bank 0)).val listHead
      ([half].map fun q => (childNode X older cap q.site : Word w)) := located.state.node.symm ▸ row
  have node' : ∀ q ∈ [half], childNode X older cap q.site < 2^w := by
    intro q h; exact List.mem_singleton.mp h ▸ nodeFit
  have fit' : ∀ q ∈ [half], A.base (childNode X older cap q.site) + (q.payload X).length < 2^w := by
    intro q h; rw [List.mem_singleton.mp h,Child.payload_ofHalf]; exact packetFit
  have tooShort : bs.length < ([half].flatMap (Child.payload X)).length := by
    simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,Child.payload_ofHalf] using short
  have fail := VertexStagePrefix.child_reject body locator M cp dfs saved reg done
    (linked a body locator loc dfs saved reg done M installed).2 rep [half] listHead mid atChild
    (located.oldFields.symm ▸ fields) row' strideFit node' fit' bs tooShort
  exact fun accept => fail ((first.returns bs).mp accept)

end PairSimulation.RefreshVertexAssembly

end VPVNP
end Computability
end OAI
