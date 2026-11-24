import OAI.Computability.VPVNP.PairVertexGeometrySegment
import OAI.Computability.VPVNP.PairNativeLeafSetupRun
import OAI.Computability.VPVNP.PairNativeCacheClock

/-! # Geometry-to-root-fields execution in the actual terminal vertex image -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexGeometry

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM NativeOperands VertexImage LeafSourceLoad
open scoped Fin.CommRing

attribute [local irreducible] NativeOperands.capacity NativeOperands.saved

variable (c : Constants) (degree a b : ℕ) {p r : ℕ}
  {rootFields leaf shrink refresh : Segment}
local notation "S" => segments (segment c degree a b) rootFields leaf shrink refresh
variable (A : VertexImage.Placement (segments (segment c degree a b) rootFields leaf shrink refresh) p r)
local notation "K" => block c degree a b A

private theorem dfs_disjoint {T : Part → Segment} (V : VertexImage.Placement T p r)
    (s : Fin 9) (j : Fin (T Part.geometry).privateRegs) : V.dfs s ≠ V.localRegs .geometry j :=
  V.reg.injective.ne (by simp)

private theorem saved_disjoint {T : Part → Segment} (V : VertexImage.Placement T p r)
    (s : Saved) (j : Fin (T Part.geometry).privateRegs) : V.saved s ≠ V.localRegs .geometry j :=
  V.reg.injective.ne (by simp)

/-- The execution preserves the genuine DFS stack registers and every saved
bootstrap word apart from the histogram pointer it publishes. -/
structure Ready {w : ℕ} (m : Memory w) (pub : Fin 11 → Word w) (st out : Config w p r)
    (cacheWords : Static 34 → Word w) : Prop where
  pc : out.pc = A.entry .rootFields
  persistent : out.persistent = st.persistent
  dfs : ∀ j, out.reg (A.dfs j) = st.reg (A.dfs j)
  saved : ∀ j ≠ histBase, out.reg (A.saved j) = st.reg (A.saved j)
  hist : out.reg (A.saved histBase) =
    ((NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m).histBase : Word w)
  geometry : let R := NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m
    LeafGeometryLoad.Stored (pub 6).val (NativeFrame.frameBase R) out.privateMem
      (NativeFrame.leafWords degree pub (st.reg (A.saved header)) (st.reg (A.saved roleOffset)) m)
  fields : ∀ j : Fin 12, let R := NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m
    out.privateMem ((NativeFrame.frameBase R+j.val : ℕ) : Word w) =
      NativeFrame.fields degree pub (st.reg (A.saved header)) (st.reg (A.saved roleOffset)) m j
  cache : Cached (NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m).cacheBase out.privateMem cacheWords
  outside : ∀ key : Word w, let R := NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m
    key ≠ pub 6 → (key.val < NativeFrame.frameBase R ∨ NativeFrame.frameBase R+12 ≤ key.val) →
      (key.val < R.cacheBase ∨ R.cacheBase+38 ≤ key.val) → out.privateMem key = st.privateMem key

/-- Exactly six header probes and no binary choices are charged before root-field gathering. -/
theorem charges {w : ℕ} (header : Word w) (m : Memory w) (t : ℕ) :
    let es := NativeFrame.events degree header m ++ List.replicate (t+2) .tick
    es.length = t+degree+143 ∧ countProbes es = 6 ∧ choiceBits es = [] := by
  intro es
  obtain ⟨length,probes,bits⟩ := NativeFrame.events_cost degree header m
  obtain ⟨tp,tb⟩ := NativeFrame.tick_cost (w := w) (t+2)
  refine ⟨?_,?_,?_⟩
  · simp only [es,List.length_append,List.length_replicate,length]; omega
  · rw [show es = _ from rfl,countProbes_append,probes,tp,Nat.add_zero]
  · rw [show es = _ from rfl,Flow.choiceBits_append,bits,tb,List.nil_append]

/-- The per-vertex initializer has a linear private clock at large input
lengths, uniformly in the group's live bucket size. -/
theorem eventually_cost (B : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ H,
    work (NativeCache.args c) a b (AssemblerPublic.geometry B n H)+76+degree+143 ≤ 2*n := by
  filter_upwards [NativeCache.eventually_work_le c a b B,Filter.eventually_ge_atTop (degree+143)]
    with n workFit large H
  have bound := workFit H
  omega

variable {prog : UniversalMachine.Program} {B n H : ℕ} {i : Fin (2^(n^c.chainPower-1))}
local notation "W" => CursorBounds.wordBits B n
local notation "D₀" => CursorBounds.virtualBits B n
local notation "E₀" => roundedUp 1 4 n
local notation "g" => AssemblerPublic.geometry B n H

variable (Q : Layout (CounterPublic.spec prog c |>.lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5)))

theorem segment_run (hb : 0 < b) (hB : 1 ≤ B) (hn : 3 ≤ n) (hH : H = 2^roundedUp a b n)
    (fit : PairNativeGeometry.Fits a b n W) (hp : Q.program = prog) (hbase : Q.scratchBase = 2^D₀)
    (hf : D.Fits) (hroot : D.root.val = 0) (hw : 2 ≤ W) (hc : 2^D₀*2^E₀ < 2^W)
    (M : Machine W p r 11) (hpub : M.publicData = Pieces.word g (CounterPublic.actualPrefix prog) ∘ StageOperands.pair c)
    (install : Contains A M) (m : Memory W) (st : Config W p r) (enter : st.pc = A.entry .geometry)
    (before : (M.publicData 6).val < NativeFrame.frameBase (NativeFrame.fromHeader degree M.publicData (st.reg (A.saved header)) m))
    (room : (NativeFrame.fromHeader degree M.publicData (st.reg (A.saved header)) m).cacheBase+38 ≤ 2^W) :
    ∃ t ≤ work (NativeCache.args c) a b g+76, ∃ out,
      Ready c degree a b A m M.publicData st out (LeafVisit.cacheWords D D₀ E₀) ∧
      ∀ fuel bits, execute M.program (fuel+t+degree+143) st m bits =
        (execute M.program fuel out m bits).map
          (Flow.prependEvents (NativeFrame.events degree (st.reg (A.saved header)) m ++ List.replicate (t+2) .tick)) := by
  let emb := placement c degree a b A
  let ret := ret c degree a b A
  obtain ⟨t,ht,mid,stop,persist,hist,geom,fields,cache,rest,regs,run⟩ :=
    NativeLeafSetup.paper_run K Q D hb hB hn hH fit hp hbase hf hroot hw hc M hpub
      emb ret (linked c degree a b A M install) m st (enter.trans (entry_eq c degree a b A).symm) before room
  let out := {mid with pc := A.entry .rootFields}
  have finish : M.program.step mid = .localStep out := by
    change (M.code mid.pc).run M.publicData mid = _
    rw [stop, linked c degree a b A M install]
    rw [NativeLeafSetup.done,NativeLeafSetup.cache_row,NativeCacheTable.row_done]
    simp only [VertexGeometry.ret,Instr.resize,Instr.run,ite_self,out,VertexImage.Placement.returns]
  refine ⟨t,ht,out,⟨rfl,persist,?_,?_,hist,geom,fields,cache,rest⟩,?_⟩
  · intro j
    apply regs
    · rintro ⟨k,e⟩; exact dfs_disjoint A j _ e.symm
    · exact A.reg.injective.ne (by simp)
    · rintro ⟨k,e⟩; exact dfs_disjoint A j _ e.symm
  · intro j hj
    apply regs
    · rintro ⟨k,e⟩; exact saved_disjoint A j _ e.symm
    · exact A.saved.injective.ne hj
    · rintro ⟨k,e⟩; exact saved_disjoint A j _ e.symm
  · intro fuel bits
    have go := run (fuel+1) bits
    change execute M.program ((fuel+1)+t+degree+142) st m bits = _ at go
    rw [show fuel+t+degree+143 = (fuel+1)+t+degree+142 by omega, go,execute,finish,Option.map_map]
    congr 1
    funext rep
    simp only [Function.comp_apply,Flow.prependEvents,Report.prepend,List.replicate_succ',List.append_assoc]
    rfl

end PairSimulation.VertexGeometry

end VPVNP
end Computability
end OAI
