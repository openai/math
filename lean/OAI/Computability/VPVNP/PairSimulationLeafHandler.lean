import OAI.Computability.VPVNP.PairSimulationLeafNativeCount
import OAI.Computability.VPVNP.PairSimulationStackScratch

/-!
# The cursor-leaf handler inside the descriptor traversal

The deterministic prefix decodes the genuine site address, reads the shadow
header, runs the local routing tests, and initializes the virtual bit stacks
at cursor zero. The remaining native instructions implement the auxiliary
machine on those supplied bits. The handler returns the entire unused
choice suffix, including when the next descriptor needs no choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafHandler

open BurstRAM PrivateRAM CursorRouting CursorNetwork LeafStartup StackMachine DFS
open scoped Fin.CommRing
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

set_option synthInstance.maxSize 10000

variable {d e w W endAddr p r k : ℕ} [NeZero d]

/-- Data and effects of the deterministic leaf prefix on the supplied private
argument buffer. -/
structure Input (d e w W endAddr : ℕ) where
  /-- The cursor coordinate and site decoded from the leaf's physical node address. -/
  pos : Position d
  /-- The four half-wire buffers supplied by the parent to this cursor visit. -/
  buffers : Buffers d (2^e) w
  /-- The RAM events of the deterministic prefix before the transit return or auxiliary
  interpreter call. -/
  trace : List (Event W)
  /-- The private scratch after routing and any stack initialization needed at cursor zero. -/
  prepared : Scratch W endAddr

variable {A : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout A n a H w}
  (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
  (storage : StackMachine.Layout (Port 52 34) W)
  (load : Word W → Scratch W endAddr → Input d e w W endAddr)
  (clock : ℕ)

/-- The local routing check accepts the decoded site position and the bits read from its four
buffers. -/
abbrev Routed (x : Input d e w W endAddr) : Prop :=
  routeAccept (2^e) w x.pos (readBuffer x.buffers) = true

/-- A linked leaf visit, using the exact push footprint also for cells of
stacks later popped back to their original size. -/
noncomputable def parser : HookParser W endAddr where
  read node saved bits :=
    let x := load node saved
    if Routed x then
      if x.pos.1 = 0 then
        let bank := auxiliaryBank D hw hc x.pos x.buffers
        match parse auxiliaryCode clock auxiliaryEntry bank bits with
        | none => none
        | some result =>
          if result.accept then
            let f := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
            some (⟨node,x.trace ++ f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩,result.rest)
          else none
      else some (⟨node,x.trace,(· = saved),fun _ => x.prepared⟩,bits)
    else none

variable {M : Machine W p r k} {visit ret : Fin p} {dfs : Fin 9 ↪ Fin r}
  {pc : Option auxiliaryProcessor.State → Fin 7 → Fin p} {reg : Register (Port 52 34) ↪ Fin r}
  {m : Memory W}

/-- Native prefix specification, ending at either the verified stack
interpreter's first row or the caller's continuation for a transit site. -/
structure Preparation (domain : Word W → Scratch W endAddr → Prop) (M : Machine W p r k)
    (visit ret : Fin p) (dfs : Fin 9 ↪ Fin r) (pc : Option auxiliaryProcessor.State → Fin 7 → Fin p)
    (reg : Register (Port 52 34) ↪ Fin r) (m : Memory W) : Prop where
  deterministic : ∀ node saved, domain node saved → choiceBits (load node saved).trace = []
  run : ∀ node (c : Config W p r) top pending, domain node (scratch endAddr c.privateMem) →
    c.pc = visit → c.reg (dfs 7) = node → DFS.Represents c.privateMem top pending →
    top + pending.length = endAddr → c.reg (dfs 5) = (top : Word W) →
    c.reg (dfs 6) = (endAddr : Word W) → c.reg (dfs 3) = 1 →
    let x := load node (scratch endAddr c.privateMem)
    Routed x → ∃ mid, mid.pc = (if x.pos.1 = 0 then pc auxiliaryEntry 0 else ret) ∧
      mid.persistent = c.persistent ∧ (∀ j : Fin 9, j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 →
        mid.reg (dfs j) = c.reg (dfs j)) ∧ DFS.Represents mid.privateMem top pending ∧
      scratch endAddr mid.privateMem = x.prepared ∧
      (x.pos.1 = 0 → StackMachine.Represents storage reg mid (auxiliaryBank D hw hc x.pos x.buffers)) ∧
      ∀ fuel bits, execute M.program (fuel+x.trace.length) c m bits =
        (execute M.program fuel mid m bits).map (fun r => ⟨x.trace++r.events,r.result⟩)
  reject : ∀ node (c : Config W p r) top pending, domain node (scratch endAddr c.privateMem) →
    c.pc = visit → c.reg (dfs 7) = node → DFS.Represents c.privateMem top pending →
    top + pending.length = endAddr → c.reg (dfs 5) = (top : Word W) →
    c.reg (dfs 6) = (endAddr : Word W) → c.reg (dfs 3) = 1 →
    ¬Routed (load node (scratch endAddr c.privateMem)) → ∀ bits, ¬Returns M c m bits

/-- Exactness on the actual node and typed buffer domain, with arbitrary
independent input bits, arbitrary used scratch, and arbitrary stream suffix. -/
theorem parser_exactOn {domain : Word W → Scratch W endAddr → Prop}
    (prep : Preparation D hw hc storage load domain M visit ret dfs pc reg m)
    (linked : StackMachine.Linked M auxiliaryCode pc reg ret) (hW : 0 < W)
    (apart : ∀ i j, dfs i ≠ reg j) (above : ∀ j, endAddr ≤ storage.base j)
    (time : ∀ node saved, domain node saved → let x := load node saved
      steps 52 (auxiliary D hw hc x.pos x.buffers) ≤ clock)
    (room : ∀ node saved, domain node saved → let x := load node saved
      ∀ j, (auxiliaryBank D hw hc x.pos x.buffers j).length + clock ≤ storage.capacity) :
    (parser D hw hc storage load clock).ExactOn domain M visit ret dfs m := by
  constructor
  · intro node saved dom bits job tail read
    let x := load node saved
    let bank := auxiliaryBank D hw hc x.pos x.buffers
    have det := prep.deterministic node saved dom
    change choiceBits x.trace = [] at det
    by_cases route : Routed x
    · by_cases hz : x.pos.1 = 0
      · let f := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
        have parsed : ∃ result, parse auxiliaryCode clock auxiliaryEntry bank bits = some result ∧
            result.accept = true ∧ job = ⟨node,x.trace++f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩ ∧
            tail = result.rest := by
          change (if Routed x then _ else none) = some (job,tail) at read
          rw [ite_eq_left route,ite_eq_left hz] at read
          change (match parse auxiliaryCode clock auxiliaryEntry bank bits with
            | none => none
            | some y => if y.accept then some (⟨node,x.trace++f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩,y.rest) else none) = some (job,tail) at read
          cases h : parse auxiliaryCode clock auxiliaryEntry bank bits with
          | none => rw [h] at read; contradiction
          | some y =>
            rw [h] at read
            cases ok : y.accept with
            | false => simp [ok] at read
            | true =>
              simp only [ok,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at read
              exact ⟨y,rfl,ok,read.1.symm,read.2.symm⟩
        obtain ⟨y,hy,ok,rfl,rfl⟩ := parsed
        have splitBits := (footprint_parse storage hy ok).1
        refine ⟨rfl,rfl,?_,?_⟩
        · simpa only [PrimedInputRAM.Flow.choiceBits_append,det,List.nil_append] using splitBits
        · intro c top pending enabled atPC nodeReg stack atEnd topReg endReg one
          change scratch endAddr c.privateMem = saved at enabled
          obtain ⟨mid,dst,persist,keep,st,sc,represented,start⟩ := prep.run node c top pending
            (enabled ▸ dom) atPC nodeReg stack atEnd topReg endReg one (by rwa [enabled])
          rw [enabled] at dst sc represented start
          have stops := (auxiliary_closed D hw hc x.pos x.buffers hz route clock (time _ _ dom)).2
          obtain ⟨out,run,retpc,_,mem,frame⟩ := footprint_native linked hW
            (fun _ _ h j => reachable_capacity stops (room _ _ dom) h j) hy ok mid
            (by simpa [x,hz] using dst) (represented hz)
          have regs (j : Fin 9) (h : j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7) :=
            (frame.dfsReg dfs apart j).trans (keep j h)
          refine ⟨out,retpc,(regs 7 (by decide)).trans nodeReg,(regs 5 (by decide)).trans topReg,
            (regs 6 (by decide)).trans endReg,(regs 3 (by decide)).trans one,frame.persistent.trans persist,
            frame.keepsPending above atEnd st,?_,?_⟩
          · rw [mem,Footprint.scratch_applyWrites,sc]
          · intro fuel more
            change execute M.program (fuel+(x.trace++f.events).length) c m (choiceBits (x.trace++f.events)++more) = _
            rw [PrimedInputRAM.Flow.choiceBits_append,det,List.nil_append,List.length_append,
              show fuel+(x.trace.length+f.events.length)=(fuel+f.events.length)+x.trace.length by omega,
              start,run.execute]
            simp only [Option.map_map,Function.comp_def,List.append_assoc]; rfl
      · have ht : job = ⟨node,x.trace,(· = saved),fun _ => x.prepared⟩ ∧ tail = bits := by
          simpa only [parser,show load node saved = x from rfl,ite_eq_left route,ite_eq_right hz,Option.some.injEq,Prod.mk.injEq] using read.symm
        obtain ⟨rfl,rfl⟩ := ht
        refine ⟨rfl,rfl,by simp [det],?_⟩
        intro c top pending enabled atPC nodeReg stack atEnd topReg endReg one
        change scratch endAddr c.privateMem = saved at enabled
        obtain ⟨mid,dst,persist,keep,st,sc,_,start⟩ := prep.run node c top pending
          (enabled ▸ dom) atPC nodeReg stack atEnd topReg endReg one (by rwa [enabled])
        rw [enabled] at dst sc start
        refine ⟨mid,?_,(keep 7 (by decide)).trans nodeReg,(keep 5 (by decide)).trans topReg,
          (keep 6 (by decide)).trans endReg,(keep 3 (by decide)).trans one,persist,st,sc,?_⟩
        · simpa only [show load node saved = x from rfl,hz,↓reduceIte] using dst
        · intro fuel more
          simpa only [det,List.nil_append] using start fuel more
    · simp only [parser,show load node saved = x from rfl,ite_eq_right route,reduceCtorEq] at read
  · intro node bits c top pending dom atPC nodeReg stack atEnd topReg endReg one fail
    let saved := scratch endAddr c.privateMem
    let x := load node saved
    let bank := auxiliaryBank D hw hc x.pos x.buffers
    by_cases route : Routed x
    · obtain ⟨mid,dst,_,_,_,_,represented,start⟩ := prep.run node c top pending dom atPC nodeReg stack
        atEnd topReg endReg one route
      by_cases hz : x.pos.1 = 0
      · have bad : acceptPrefix auxiliaryCode clock auxiliaryEntry bank bits = none := by
          cases h : parse auxiliaryCode clock auxiliaryEntry bank bits with
          | none => simp [acceptPrefix,haltPrefix,h]
          | some y =>
            cases ok : y.accept with
            | false => simp [acceptPrefix,haltPrefix,h,ok]
            | true =>
              simp only [parser,show load node (scratch endAddr c.privateMem) = x from rfl,ite_eq_left route,ite_eq_left hz,
                show auxiliaryBank D hw hc x.pos x.buffers = bank from rfl,h,ok,↓reduceIte,reduceCtorEq] at fail
        have stops := (auxiliary_closed D hw hc x.pos x.buffers hz route clock (time _ _ dom)).2
        have reject := rejects_returns linked hW (fun _ _ h j => reachable_capacity stops (room _ _ dom) h j)
          stops mid (by simpa only [show load node (scratch endAddr c.privateMem) = x from rfl,hz,↓reduceIte] using dst)
          (represented hz) m bits bad
        exact fun ok => reject ((returns_prefix (fun fuel => start fuel bits)).mp ok)
      · simp only [parser,show load node (scratch endAddr c.privateMem) = x from rfl,ite_eq_left route,ite_eq_right hz,reduceCtorEq] at fail
    · exact prep.reject node c top pending dom atPC nodeReg stack atEnd topReg endReg one route bits

end PairSimulation.LeafHandler

end VPVNP
end Computability
end OAI
