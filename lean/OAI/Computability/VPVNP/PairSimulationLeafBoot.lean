import OAI.Computability.VPVNP.PairSimulationLeafBootSources
import OAI.Computability.VPVNP.PairSimulationLeafArena

/-!
# Initializing a cursor-zero leaf from its four half buffers and operand cache

The parent call supplies the decoded node and site addresses, the full O
header, and the cache base. Its private RAM reads the 38 cached words,
computes the stride, and executes the scalar and incident instruction
tables. The result gives the entire private scratch after the last write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBoot

open BurstRAM PrivateRAM RAMTape LeafStartup StackMachine LeafRegisterBank PrimedCounter.GuessWord
open CursorNetwork CursorRouting RAMLayout
open scoped Fin.CommRing

set_option synthInstance.maxSize 10000

variable {A : PrimedInputRAM.Lengths} {n a H s w d e p r k : ℕ} [NeZero d] {Q : PrimedInputRAM.Layout A n a H w}
variable (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
  (v : Site d) (buf : Buffers d (2^e) w)

/-- Instruction count for cursor-zero startup, including the fixed cache and capacity setup,
scalar stack initialization, and incident-bit copy. -/
noncomputable def ticks := 89 + scalarTicks D hw hc (0,v) buf + LeafIncidentMachine.ticks v (2^e) w

omit [NeZero d] in
/-- Word addresses of the four slices precede the private stack arena,
so every word survives the allocation and scalar writes. -/
private theorem still_stored (R : LeafArena.Regions) (L : Layout ScalarPort w) (node : ℕ)
    (before : node+4*ramPayloadWidth d (2^e) w ≤ R.stackBase) (upper : R.stackBase < 2^w)
    (above : ∀ j, R.stackBase ≤ L.base j) (old : Word w → Word w) (s : Stacks ScalarPort)
    (stored : LeafIncidentLoad.Stored (LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w)) buf old) :
    LeafIncidentLoad.Stored (LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w)) buf
      (LeafLoadedBank.memory L s old) := by
  intro port i
  apply (LeafIncidentBank.memory_outside L s old _ ?_).trans (stored port i)
  intro j
  apply Or.inl
  have hi := i.isLt
  have hl : LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w) port + i.val < R.stackBase := by
    cases port with | outgoing side | incoming side => cases side <;> simp only [LeafIncidentMachine.base] <;> omega
  change ((LeafIncidentMachine.base node _ port + i.val) % 2^w) < L.base j
  rw [Nat.mod_eq_of_lt (hl.trans upper)]
  exact hl.trans_le (above j)

theorem run (M : Machine w p r k) (pc : Label → Fin p) (reg : Reg ↪ Fin r) (nPub : Fin k) (done : Fin p)
    (link : Linked pc reg nPub done M) (R : LeafArena.Regions) (node : ℕ)
    (fit : R.stackBase+Fintype.card ScalarPort*n^40 < 2^w) (before : node+4*ramPayloadWidth d (2^e) w ≤ R.stackBase)
    (c : Config w p r) (entry : c.pc = pc (.pre 0)) (hnode : c.reg (nodeBase reg) = (node : Word w))
    (cachePtr : c.reg (cacheBase reg) = (R.cacheBase : Word w)) (hn : M.publicData nPub = (n : Word w))
    (address : c.reg (sources reg .address) = (v.val : Word w))
    (header : c.reg (sources reg .header) = D.initial v)
    (cache : LeafSourceLoad.Cached R.cacheBase c.privateMem
      (fun j => sourceWord (auxiliary D hw hc (0,v) buf) D.pub j.dest))
    (stored : LeafIncidentLoad.Stored (LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w)) buf c.privateMem)
    (room : ∀ j, (bank 52 (auxiliary D hw hc (0,v) buf) D.pub j).length ≤ n^40)
    {top endAddr : ℕ} (pending : List (Word w)) (htop : top+pending.length = endAddr)
    (previous : DFS.Represents c.privateMem top pending) (low : endAddr ≤ R.arguments.start) :
    let L := R.layout portOrder.symm.toEmbedding (n^40) fit
    let full := bank 52 (auxiliary D hw hc (0,v) buf) D.pub
    ∃ out, Prefix M c (List.replicate (ticks D hw hc v buf) .tick) out ∧ out.pc = done ∧
      Represents L (stack reg) out full ∧ out.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      out.privateMem = LeafLoadedBank.memory L full c.privateMem ∧
      DFS.Represents out.privateMem top pending ∧
      DFS.scratch endAddr out.privateMem = LeafLoadedBank.scratch L full (DFS.scratch endAddr c.privateMem) := by
  intro L full
  let x := auxiliary D hw hc (0,v) buf
  let scalarBank := scalarInput D hw hc (0,v) buf
  have addr : c.reg (sources reg .address) = x.addrWord := by
    rw [address]; apply Fin.ext
    exact Nat.mod_eq_of_lt x.addrWord.isLt
  obtain ⟨start,pre,hpc,hvals,hcursor,hstride,memA,stateA,nodeA,regsA⟩ :=
    source_prefix pc reg nPub done M x D.pub n R.cacheBase link c entry addr header rfl cachePtr cache hn
  have scalarRoom (j : ScalarPort) : (scalarBank j).length ≤ n^40 := by
    change (fieldBits x D.pub (scalarField (field j))).length ≤ _
    by_cases hi : field j = .incident
    · simp [scalarField,hi,fieldBits]
    · rw [scalarField,ite_eq_right hi]; exact room j
  have sl (j : ScalarLabel) : M.code ((pc ∘ Label.scalar) j) =
      LeafPortTable.instruction field (pc ∘ Label.scalar) (scalar reg) (pc (.incident (.inl 0))) scalarRows j :=
    link (.scalar j)
  obtain ⟨mid,runS,sitePC,rep,sourcesReady,stateS,regsS,memS⟩ :=
    scalar_start D hw hc (0,v) buf M (scalar reg) (pc ∘ Label.scalar) (pc (.incident (.inl 0))) R.stackBase
      (n^40) fit sl start hpc hcursor hstride hvals scalarRoom
  change Represents L (stack reg) mid scalarBank at rep
  change mid.privateMem = LeafLoadedBank.memory L scalarBank start.privateMem at memS
  rw [memA] at memS
  have pNode := (regsS (nodeBase reg) (by rintro ⟨i,h⟩; simp [nodeBase] at h)).trans (nodeA.trans hnode)
  have ready : LeafIncidentGeometry.Ready d (2^e) w v.val node (L.base incident) (mid.reg ∘ geometry reg) := by
    refine ⟨sourcesReady.d,?_,sourcesReady.bucket,sourcesReady.width,pNode,?_⟩
    · change mid.reg (sources reg .address) = _
      have val := sourcesReady.address
      change mid.reg (sources reg .address) = x.addrWord at val
      rw [val]
      exact Fin.ext (Nat.mod_eq_of_lt x.addrWord.isLt).symm
    · exact (rep.bases incident).trans (by simp [Layout.address])
  have upper := (Nat.le_add_right R.stackBase _).trans_lt fit
  have above (j : ScalarPort) := R.stack_above portOrder.symm.toEmbedding (n^40) fit j
  have stored' : LeafIncidentLoad.Stored (LeafIncidentMachine.base node (ramPayloadWidth d (2^e) w)) buf mid.privateMem :=
    memS ▸ still_stored buf R L node before upper above c.privateMem scalarBank stored
  have fieldRoom : width d (2^e) w ≤ n^40 := by
    have h := room incident
    change (List.ofFn (RAMLayout.incidentBits x.sends x.v)).length ≤ n^40 at h
    simpa only [List.length_ofFn] using h
  have hDW := (Nat.le_add_right d e).trans_lt x.hcap
  have incRows : LeafIncidentMachine.Linked M (pc ∘ Label.incident) (geometry reg) done := fun j => link (.incident j)
  obtain ⟨out,runI,physical,fullRep,exactMem,kept,scratch⟩ := LeafIncidentBank.machine_run D hw hc v buf L
    (stack reg) (geometry reg) (pc ∘ Label.incident) M done incRows node mid sitePC ready hDW stored'
    (before.trans upper.le) (.inl (before.trans (above incident))) rfl (protect reg) c.privateMem pending htop previous
    (R.stack_above_dfs _ _ fit low) rep scalarRoom fieldRoom memS
  have all := (pre.append runS).append runI
  rw [← List.replicate_add,← List.replicate_add] at all
  refine ⟨out,all,physical.pc,fullRep,physical.persistent.trans (stateS.trans stateA),?_,exactMem,kept,scratch⟩
  intro i hi
  have ne (j : Reg) : i ≠ reg j := fun he => hi ⟨j,he.symm⟩
  exact (physical.frame i (fun j _ => ne (geometryName j))).trans
    ((regsS i (fun ⟨j,h⟩ => hi ⟨.inl j,h⟩)).trans (regsA i hi))

end PairSimulation.LeafBoot

end VPVNP
end Computability
end OAI
