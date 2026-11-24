import OAI.Computability.VPVNP.PairVertexImage
import OAI.Computability.VPVNP.PairPendingArguments

/-! # Executing the private geometry, role-dispatch and counter rows -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS PrimedCounter.GuessWord NodeArguments
open scoped Fin.CommRing

variable {W p r : ℕ} {S : Part → Segment} {A : Placement S p r} {M : Machine W p r 11}

theorem geometry_run {pc : Fin 3 → Fin p} {endReg dst tmp : Fin r} {offset : Word W} {done : Fin p}
    (linked : ∀ i, M.code (pc i) = geometryRows pc endReg dst tmp offset done i)
    (apart : dst ≠ tmp) (c : Config W p r) (hc : c.pc = pc 0) :
    ∃ out, Prefix M c (List.replicate 3 .tick) out ∧ out.pc = done ∧
      out.reg dst = c.privateMem (c.reg endReg) + offset ∧
      (∀ j, j ≠ dst → j ≠ tmp → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  have step (i : Fin 3) (d : Config W p r) (hd : d.pc = pc i) :
      M.program.step d = (geometryRows pc endReg dst tmp offset done i).run M.publicData d := by
    change (M.code d.pc).run _ _ = _
    rw [hd,linked]
  let c₁ := c.put (pc 1) dst (c.privateMem (c.reg endReg))
  let c₂ := c₁.put (pc 2) tmp offset
  let out := c₂.put done dst (c₂.reg dst + c₂.reg tmp)
  have run : Prefix M c (List.replicate 3 .tick) out :=
    .tick (step 0 c hc) (.tick (step 1 c₁ rfl) (.tick (step 2 c₂ rfl) (.nil out)))
  exact ⟨out, run, rfl, by simp [out,c₂,c₁,Config.put,Function.update_of_ne apart],
    fun j hd ht => by simp [out,c₂,c₁,Config.put,Function.update_of_ne hd,Function.update_of_ne ht],rfl,rfl⟩

/-- The dispatcher and flush reread these two slots from scratch. Only the
words at the designated addresses matter to their operation. -/
structure ResidentGeometry {endAddr : ℕ} (s : Scratch W endAddr) (G offset hist : Word W) : Prop where
  endFit : endAddr < 2^W
  roleAbove : endAddr ≤ (G+10).val
  histAbove : endAddr ≤ (G+11).val
  pointer : rawScratch s (endAddr : Word W) = G
  role : rawScratch s (G+10) = offset
  histogram : rawScratch s (G+11) = hist

private theorem resident_read {endAddr : ℕ} (mem : Word W → Word W) (G offset hist : Word W)
    (stored : ResidentGeometry (scratch endAddr mem) G offset hist) :
    mem (endAddr : Word W) = G ∧ mem (G+10) = offset ∧ mem (G+11) = hist := by
  have h : endAddr ≤ (endAddr : Word W).val := (Nat.mod_eq_of_lt stored.endFit).ge
  exact ⟨by simpa only [rawScratch,dite_eq_left h,scratch] using stored.pointer,
    by simpa [rawScratch,scratch,stored.roleAbove] using stored.role,
    by simpa [rawScratch,scratch,stored.histAbove] using stored.histogram⟩

/-- The three private geometry-load ticks followed by the external role-word dispatch for a
popped node. -/
def dispatchEvents (m : Memory W) (offset node : Word W) : List (Event W) :=
  List.replicate 3 .tick ++ NodeDispatch.events m offset node

theorem dispatchEvents_cost (m : Memory W) (offset node : Word W) :
    countProbes (dispatchEvents m offset node) = 1 ∧ (dispatchEvents m offset node).length ≤ 9 ∧
      choiceBits (dispatchEvents m offset node) = [] := by
  obtain ⟨probes,time,choices⟩ := NodeDispatch.events_cost m offset node
  exact ⟨probes, by simp only [dispatchEvents,List.length_append,List.length_replicate]; omega, choices⟩

/-- One actual external tag probe selects the same handler as the recorded
role. The geometry pointer and both data words come from the private packet
domain, so every unused host register may hold arbitrary data. -/
theorem dispatch_run (linked : Contains A M) {endAddr : ℕ} (G offset hist : Word W)
    (c : Config W p r) (hc : c.pc = A.core (.roleBase 0)) (h1 : c.reg (A.dfs 3) = 1)
    (hend : c.reg (A.dfs 6) = (endAddr : Word W))
    (stored : ResidentGeometry (scratch endAddr c.privateMem) G offset hist) (m : Memory W) :
    let node := c.reg (A.dfs 7)
    ∃ out, out.pc = A.entry (rolePart (NodeDispatch.role (m (offset+node).val))) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      (∀ j, j ≠ A.dfs 0 → j ≠ A.dfs 1 → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+(dispatchEvents m offset node).length) c m bs =
        (execute M.program fuel out m bs).map (fun rep => ⟨dispatchEvents m offset node ++ rep.events,rep.result⟩) := by
  intro node
  obtain ⟨pointer,role,_⟩ := resident_read c.privateMem G offset hist stored
  obtain ⟨mid,pre,pc,addr,regs,mem,persist⟩ := geometry_run (roleBase_linked A M linked)
    (A.dfs.injective.ne (by decide)) c hc
  have head : M.program.step mid = .localStep (mid.put (A.rolePC 1) (A.dfs 0) offset) := by
    change (M.code mid.pc).run _ _ = _
    rw [pc,dispatch_linked A M linked]
    change CallAction.localStep (mid.put (A.rolePC 1) (A.dfs 0) (mid.privateMem (mid.reg (A.dfs 0)))) = _
    rw [addr,hend,pointer,mem,role]
  have tail (i : Fin 6) (hi : i ≠ 0) :
      M.code (A.rolePC i) = NodeDispatch.instruction A.rolePC A.dfs 0 (A.entry ∘ rolePart) i := by
    rw [dispatch_linked A M linked, dispatchRows, ite_eq_right hi]
  have unit := (regs _ (A.dfs.injective.ne (by decide : (3:Fin 9) ≠ 0))
    (A.dfs.injective.ne (by decide : (3:Fin 9) ≠ 1))).trans h1
  obtain ⟨out,hd,hm,hs,keep,run⟩ := NodeDispatch.enter_loaded offset mid head tail unit m
  have num : mid.reg (A.dfs 7) = node :=
    regs _ (A.dfs.injective.ne (by decide)) (A.dfs.injective.ne (by decide))
  rw [num] at hd run
  refine ⟨out,hd,hm.trans mem,hs.trans persist,fun j h0 h1 => (keep _ h0 h1).trans (regs _ h0 h1),?_⟩
  intro fuel bs
  have start := pre.execute (fuel+(NodeDispatch.events m offset node).length) m bs
  change execute M.program (fuel+(NodeDispatch.events m offset node).length+3) c m bs = _ at start
  rw [dispatchEvents,List.length_append,List.length_replicate,show fuel+(3+(NodeDispatch.events m offset node).length) = fuel+(NodeDispatch.events m offset node).length+3 by omega,start,run]
  simp only [Option.map_map,Function.comp_def,List.append_assoc]

/-- The remaining seven flush-setup rows load the three public sizes and
the private histogram pointer. The seven counter-loop rows then perform
the actual shared read/add/write sequence on every template component. -/
theorem flush_run_events (linked : Contains A M) {endAddr g : ℕ} (G offset : Word W)
    (c : Config W p r) (hc : c.pc = A.core (.histBase 0)) (hend : c.reg (A.dfs 6) = (endAddr : Word W))
    (base grammar src : ℕ) (stored : ResidentGeometry (scratch endAddr c.privateMem) G offset (src : Word W))
    (hbase : M.publicData 4 = (base : Word W)) (hgrammar : M.publicData 5 = (grammar : Word W))
    (hg : M.publicData 9 = (g : Word W)) (h : Fin g → ℕ)
    (hpriv : ∀ i : Fin g, c.privateMem ((src+i.val : ℕ) : Word W) = (h i : Word W))
    (hsrc : src+g < 2^W) (hdst : base+grammar+g < 2^W) (m : Memory W) :
    ∃ out es, out.pc = A.entry .finish ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      es = List.replicate 10 .tick ++ Counters.events c.privateMem m src (base+grammar) g ∧
      es.length = 7*g+11 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = Counters.addHistogram base grammar h m ∧
      ∀ fuel bs, execute M.program (fuel+7*g+11) c m bs =
        (execute M.program fuel out (Counters.addHistogram base grammar h m) bs).map
          (fun rep => ⟨es ++ rep.events,rep.result⟩) := by
  obtain ⟨pointer,_,hist⟩ := resident_read c.privateMem G offset (src : Word W) stored
  obtain ⟨mid,geom,hpc,addr,_,mem,persist⟩ := geometry_run (histBase_linked A M linked)
    (A.counter.injective.ne (by decide)) c hc
  let pc := A.flushStartPC
  let reg := A.counter
  have step (i : Fin 7) (d : Config W p r) (hd : d.pc = pc i) :
      M.program.step d = (flushStartRows pc reg (A.flushPC 0) i).run M.publicData d := by
    change (M.code d.pc).run _ _ = _
    rw [hd,flushStart_linked A M linked]
  let c₁ := mid.put (pc 1) (reg 0) (M.publicData 4)
  let c₂ := c₁.put (pc 2) (reg 4) (M.publicData 5)
  let c₃ := c₂.put (pc 3) (reg 0) (c₂.reg (reg 0)+c₂.reg (reg 4))
  let c₄ := c₃.put (pc 4) (reg 1) (M.publicData 9)
  let c₅ := c₄.put (pc 5) (reg 1) (c₄.reg (reg 0)+c₄.reg (reg 1))
  let c₆ := c₅.put (pc 6) (reg 2) (c₅.privateMem (c₅.reg (reg 2)))
  let start := c₆.put (A.flushPC 0) (reg 3) 1
  have init : Prefix M mid (List.replicate 7 .tick) start :=
    .tick (step 0 mid hpc) (.tick (step 1 c₁ rfl) (.tick (step 2 c₂ rfl) (.tick (step 3 c₃ rfl)
      (.tick (step 4 c₄ rfl) (.tick (step 5 c₅ rfl) (.tick (step 6 c₆ rfl) (.nil _)))))))
  have pre : Prefix M c (List.replicate 10 .tick) start := geom.append init
  have hr : start.reg (reg 0) = ((base+grammar : ℕ) : Word W) := by
    simp [start,c₆,c₅,c₄,c₃,c₂,c₁,Config.put,hbase,hgrammar]
  have he : start.reg (reg 1) = ((base+grammar+g : ℕ) : Word W) := by
    simp [start,c₆,c₅,c₄,c₃,c₂,c₁,Config.put,hbase,hgrammar,hg]
  have ptr : mid.reg (reg 2) = G+11 := by rw [addr,hend,pointer]
  have hs : start.reg (reg 2) = (src : Word W) := by
    simp [start,c₆,c₅,c₄,c₃,c₂,c₁,Config.put,ptr,mem,hist]
  obtain ⟨out,es,dst,hmem,st,logs,len,probes,choices,upd,run⟩ :=
    Counters.execute_vertex_events (core_linked A M linked).2.2 start rfl base grammar src h
      (by intro i; change mid.privateMem _ = _; rw [mem]; exact hpriv i)
      hsrc hdst hr he hs (by change start.reg (reg 3) = 1; simp [start,Config.put]) m
  refine ⟨out,List.replicate 10 .tick ++ es,dst,hmem.trans mem,st.trans persist,
    by rw [logs]; change _ ++ Counters.events mid.privateMem _ _ _ _ = _; rw [mem],
    by simp [len],probes,choices,upd,?_⟩
  intro fuel bs
  have lead := pre.execute (fuel+7*g+1) m bs
  change execute M.program (fuel+7*g+1+10) c m bs = _ at lead
  rw [show fuel+7*g+11=fuel+7*g+1+10 by omega,lead,run]
  simp only [Option.map_map,Function.comp_def,List.append_assoc]

theorem flush_run (linked : Contains A M) {endAddr g : ℕ} (G offset : Word W)
    (c : Config W p r) (hc : c.pc = A.core (.histBase 0)) (hend : c.reg (A.dfs 6) = (endAddr : Word W))
    (base grammar src : ℕ) (stored : ResidentGeometry (scratch endAddr c.privateMem) G offset (src : Word W))
    (hbase : M.publicData 4 = (base : Word W)) (hgrammar : M.publicData 5 = (grammar : Word W))
    (hg : M.publicData 9 = (g : Word W)) (h : Fin g → ℕ)
    (hpriv : ∀ i : Fin g, c.privateMem ((src+i.val : ℕ) : Word W) = (h i : Word W))
    (hsrc : src+g < 2^W) (hdst : base+grammar+g < 2^W) (m : Memory W) :
    ∃ out es, out.pc = A.entry .finish ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      es.length = 7*g+11 ∧ countProbes es = 2*g ∧ choiceBits es = [] ∧
      after m es = Counters.addHistogram base grammar h m ∧
      ∀ fuel bs, execute M.program (fuel+7*g+11) c m bs =
        (execute M.program fuel out (Counters.addHistogram base grammar h m) bs).map
          (fun rep => ⟨es ++ rep.events,rep.result⟩) := by
  obtain ⟨out, es, pc, mem, state, _, rest⟩ :=
    flush_run_events linked G offset c hc hend base grammar src stored hbase hgrammar hg h hpriv hsrc hdst m
  exact ⟨out, es, pc, mem, state, rest⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
