import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherCode
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherReads
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-! # Execution of both terminal slot scans

The slot cursor counts empty slots as well as positive-width slots. It reads
the shared directory, copies exactly one external word per wire bit, and
preserves the private memory outside its destination interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w p r : ℕ} {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r}
  {done : Fin p} {m : Memory w} {c d e : Config w p r}

theorem Prefix.trans {xs ys : List (Event w)} (hx : Prefix M m c xs d) (hy : Prefix M m d ys e) :
    Prefix M m c (xs++ys) e := by
  intro f bs
  rw [List.length_append,show f+(xs.length+ys.length)=(f+ys.length)+xs.length by omega,hx,hy]
  simp [Option.map_map,Function.comp_def]

theorem Prefix.tick (h : M.program.step c = .localStep d) : Prefix M m c [.tick] d := by
  intro f bs
  simp only [List.length_cons,List.length_nil,zero_add,execute,h]
  rfl

theorem Frame.trans (h₁ : Frame reg c d) (h₂ : Frame reg d e) : Frame reg c e :=
  ⟨h₂.1.trans h₁.1,fun i h => (h₂.2 i h).trans (h₁.2 i h)⟩

theorem Saved.transport {L : Layout} (h : Saved L reg c) (f : Frame reg c d) : Saved L reg d := by
  have stable (i : Fin 11) : d.reg (reg (save i)) = c.reg (reg (save i)) :=
    f.2 _ (fun j => reg.injective.ne (Sum.inl_ne_inr : tmp j ≠ save i))
  exact ⟨(stable _).trans h.ordinal,(stable _).trans h.root,(stable _).trans h.sites,
    (stable _).trans h.slots,(stable _).trans h.widths,(stable _).trans h.incoming,
    (stable _).trans h.prefixBase,(stable _).trans h.wires⟩

/-- Certifies the exact event count and external probe count of a gather trace, together with
preservation of external memory and an empty choice-bit trace. -/
structure Cost (es : List (Event w)) (ticks reads : ℕ) : Prop where
  time : es.length = ticks
  probes : countProbes es = reads
  after_eq : ∀ mem, after mem es = mem
  bits : choiceBits es = []

theorem Cost.append {xs ys : List (Event w)} {t₁ t₂ r₁ r₂ : ℕ} (hx : Cost xs t₁ r₁) (hy : Cost ys t₂ r₂) :
    Cost (xs++ys) (t₁+t₂) (r₁+r₂) := by
  refine ⟨by simp [hx.time,hy.time],by rw [countProbes_append,hx.probes,hy.probes],?_,?_⟩
  · intro mem
    rw [after,List.foldl_append]
    change after (after mem xs) ys = mem
    rw [hx.after_eq,hy.after_eq]
  · rw [PrimedInputRAM.Flow.choiceBits_append,hx.bits,hy.bits]; rfl

theorem Cost.tick : Cost ([.tick] : List (Event w)) 1 0 := ⟨rfl,rfl,fun _ => rfl,rfl⟩

theorem Cost.replicate_tick (n : ℕ) : Cost (List.replicate n (.tick : Event w)) n 0 := by
  induction n with
  | zero => exact ⟨rfl,rfl,fun _ => rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ,Nat.one_add, Nat.zero_add,List.singleton_append] using Cost.tick.append ih

theorem arc_cost (mem : Memory w) (s n : ℕ) : Cost (EndpointBits.events mem s n) (5*n+1) n := by
  induction n generalizing s with
  | zero => exact Cost.tick
  | succ n ih =>
    have h : Cost ([.tick,.read (s : Word w) (mem s),.tick,.tick,.tick] : List (Event w)) 5 1 :=
      ⟨rfl,rfl,fun _ => rfl,rfl⟩
    simpa only [EndpointBits.events,show 5 + (5*n+1) = 5*(n+1)+1 by omega,Nat.one_add] using h.append (ih (s+1))

/-- Slot-loop invariant for the next field to gather. It records the private write cursor, the
unit increment, and the current, first and exclusive-end slot indices. -/
structure Cursor (L : Layout) (reg : Reg ↪ Fin r) (c : Config w p r) (j dst : ℕ) : Prop where
  dest : c.reg (reg (tmp 2)) = (dst : Word w)
  one : c.reg (reg (tmp 3)) = 1
  slot : c.reg (reg (tmp 5)) = (L.index j : Word w)
  stop : c.reg (reg (tmp 6)) = (L.index L.degree : Word w)
  first : c.reg (reg (tmp 7)) = (L.index 0 : Word w)

/-- Postcondition for the two straight-line directory-read blocks. -/
def Headers (L : Layout) (M : Machine w p r 11) (m : Memory w) (pc : PC → Fin p) (reg : Reg ↪ Fin r) :=
  ∀ b j, j < L.degree → ∀ c : Config w p r, c.pc = pc (.header b (firstHeader b)) →
    Saved L reg c → c.reg (reg (tmp 5)) = (L.index j : Word w) → ∃ out es,
    out.pc = pc (.bits b 0) ∧ Frame reg c out ∧ out.privateMem = c.privateMem ∧
    out.reg (reg (tmp 0)) = (L.start m b j : Word w) ∧
    out.reg (reg (tmp 1)) = ((L.start m b j+L.width m b j : ℕ) : Word w) ∧
    (∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 4 → out.reg (reg (tmp i)) = c.reg (reg (tmp i))) ∧
    Cost es (if b then 8 else 7) (if b then 3 else 2) ∧ Prefix M m c es out

/-- Directory-read postcondition including the addresses of the same execution. -/
def HeadersReads (P : ℕ → Prop) (L : Layout) (M : Machine w p r 11) (m : Memory w)
    (pc : PC → Fin p) (reg : Reg ↪ Fin r) :=
  ∀ b j, j < L.degree → ∀ c : Config w p r, c.pc = pc (.header b (firstHeader b)) →
    Saved L reg c → c.reg (reg (tmp 5)) = (L.index j : Word w) → ∃ out es,
    out.pc = pc (.bits b 0) ∧ Frame reg c out ∧ out.privateMem = c.privateMem ∧
    out.reg (reg (tmp 0)) = (L.start m b j : Word w) ∧
    out.reg (reg (tmp 1)) = ((L.start m b j+L.width m b j : ℕ) : Word w) ∧
    (∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 4 → out.reg (reg (tmp i)) = c.reg (reg (tmp i))) ∧
    Cost es (if b then 8 else 7) (if b then 3 else 2) ∧ Reads P es ∧ Prefix M m c es out

private theorem headersReads_true {L : Layout} (h : Headers L M m pc reg) :
    HeadersReads (fun _ ↦ True) L M m pc reg := by
  intro b j hj cur hc saved slot
  obtain ⟨out,es,hpc,hf,hm,hs,he,hr,hcost,run⟩ := h b j hj cur hc saved slot
  exact ⟨out,es,hpc,hf,hm,hs,he,hr,hcost,fun _ _ _ ↦ trivial,run⟩

private theorem step_at (hl : Linked M pc reg done) (i : PC) (hc : c.pc=pc i) :
    M.program.step c = (rows pc reg (bitRegs reg) done i).run M.publicData c := by
  simp only [Machine.program,hc,hl i]

/-- A nonempty slot scan iteration, including its cursor comparison and increment.
The bit loop still performs an exit comparison when the selected width is zero. -/
theorem field_run_reads (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (P : ℕ → Prop) (readable : L.Readable m P) (headers : HeadersReads P L M m pc reg)
    (b : Bool) (j dst : ℕ) (hj : j < L.degree)
    (hd : dst+L.width m b j < 2^w) (c : Config w p r) (hc : c.pc=pc (.scan b))
    (saved : Saved L reg c) (cur : Cursor L reg c j dst) :
    ∃ out es, out.pc=pc (.scan b) ∧ Frame reg c out ∧
      out.privateMem = Layout.placed dst (L.field m b j) c.privateMem ∧
      Cursor L reg out (j+1) (dst+L.width m b j) ∧
      Cost es ((if b then 11 else 10)+5*L.width m b j) (L.width m b j+(if b then 3 else 2)) ∧
      Reads P es ∧ Prefix M m c es out := by
  let head := {c with pc := pc (.header b (firstHeader b))}
  have hlt : L.index j < L.index L.degree := Nat.add_lt_add_left hj _
  have hne : c.reg (reg (tmp 5)) ≠ c.reg (reg (tmp 6)) := by
    rw [cur.slot,cur.stop]
    intro eqn
    have vals := congrArg Fin.val eqn
    change L.index j % (2^w) = L.index L.degree % (2^w) at vals
    rw [Nat.mod_eq_of_lt (hlt.trans fit.lastIndex),Nat.mod_eq_of_lt fit.lastIndex] at vals
    exact hlt.ne vals
  have first : Prefix M m c [.tick] head := Prefix.tick (by
    rw [step_at hl _ hc]; simp [rows,Instr.run,hne,head])
  have fhead : Frame reg c head := ⟨rfl,fun _ _ => rfl⟩
  obtain ⟨pre,hs,hpc,hframe,hpriv,src,hend,rest,hcost,hreads,hprefix⟩ :=
    headers b j hj head rfl (saved.transport fhead) cur.slot
  have br : EndpointBits.Linked M (pc ∘ PC.bits b) (bitRegs reg) (pc (.advance b)) := fun i => hl (.bits b i)
  obtain ⟨post,hpost,hpersist,_,dest,other,priv,executeBits⟩ :=
    EndpointBits.execute_arc br pre hpc m (L.start m b j) dst (L.width m b j)
      (fit.sourceEnd b j hj) hd src hend ((rest 2 (by decide) (by decide) (by decide)).trans cur.dest)
      ((rest 3 (by decide) (by decide) (by decide)).trans cur.one)
  have postFrame : Frame reg pre post :=
    ⟨hpersist,fun i hi => other _ (hi 0).symm (hi 2).symm (hi 4).symm⟩
  have bitCost := arc_cost m (L.start m b j) (L.width m b j)
  have runBits : Prefix M m pre (EndpointBits.events m (L.start m b j) (L.width m b j)) post := by
    intro f bs
    rw [bitCost.time,← Nat.add_assoc]
    exact executeBits f bs
  have keep (i : Fin 9) (h0 : i≠0) (h1 : i≠1) (h2 : i≠2) (h4 : i≠4) :
      post.reg (reg (tmp i))=c.reg (reg (tmp i)) := by
    apply (other _ ?_ ?_ ?_).trans (rest i h0 h1 h4)
    · exact reg.injective.ne (Sum.inl_injective.ne h0)
    · exact reg.injective.ne (Sum.inl_injective.ne h2)
    · exact reg.injective.ne (Sum.inl_injective.ne h4)
  let out := post.put (pc (.scan b)) (reg (tmp 5)) (post.reg (reg (tmp 5))+post.reg (reg (tmp 3)))
  have last : Prefix M m post [.tick] out := Prefix.tick (by rw [step_at hl _ hpost]; rfl)
  have outFrame : Frame reg post out := ⟨rfl,fun i hi => Function.update_of_ne (hi 5).symm ..⟩
  have frame : Frame reg c out := Frame.trans (c:=c) hframe (postFrame.trans outFrame)
  have outKeep (i : Fin 9) (h : i≠5) : out.reg (reg (tmp i)) = post.reg (reg (tmp i)) :=
    Function.update_of_ne (reg.injective.ne (Sum.inl_injective.ne h)) ..
  have postKeep (i : Fin 9) (h : i=3 ∨ i=5 ∨ i=6 ∨ i=7) : post.reg (reg (tmp i))=c.reg (reg (tmp i)) := by
    rcases h with rfl|rfl|rfl|rfl <;> apply keep <;> decide
  let es := [.tick] ++ hs ++ EndpointBits.events m (L.start m b j) (L.width m b j) ++ [.tick]
  refine ⟨out,es,rfl,frame,?_,?_,?_,?_,((first.trans hprefix).trans runBits).trans last⟩
  · change post.privateMem = _
    rw [priv,hpriv,L.copy_field]
  · refine ⟨(outKeep 2 (by decide)).trans dest,(outKeep 3 (by decide)).trans ((postKeep 3 (by decide)).trans cur.one),?_,
      (outKeep 6 (by decide)).trans ((postKeep 6 (by decide)).trans cur.stop),
      (outKeep 7 (by decide)).trans ((postKeep 7 (by decide)).trans cur.first)⟩
    simp only [out,Config.put,Function.update_self,postKeep 5 (by decide),postKeep 3 (by decide),cur.slot,cur.one,
      Layout.index,Nat.cast_add,Nat.cast_one,add_assoc]
  · have co := ((Cost.tick.append hcost).append bitCost).append Cost.tick
    cases b <;> simpa only [Bool.false_eq_true,↓reduceIte,es,show ∀ x, 1+7+(5*x+1)+1=10+5*x by omega,
      show ∀ x, 1+8+(5*x+1)+1=11+5*x by omega,zero_add,add_zero,Nat.add_comm 2,Nat.add_comm 3] using co
  · exact (((Reads.replicate_tick P 1).append hreads).append
      (arc_reads m P _ _ (fit.sourceEnd b j hj) (readable.wire b j hj))).append (Reads.replicate_tick P 1)

theorem field_run (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (headers : Headers L M m pc reg) (b : Bool) (j dst : ℕ) (hj : j < L.degree)
    (hd : dst+L.width m b j < 2^w) (c : Config w p r) (hc : c.pc=pc (.scan b))
    (saved : Saved L reg c) (cur : Cursor L reg c j dst) :
    ∃ out es, out.pc=pc (.scan b) ∧ Frame reg c out ∧
      out.privateMem = Layout.placed dst (L.field m b j) c.privateMem ∧
      Cursor L reg out (j+1) (dst+L.width m b j) ∧
      Cost es ((if b then 11 else 10)+5*L.width m b j) (L.width m b j+(if b then 3 else 2)) ∧
      Prefix M m c es out := by
  obtain ⟨out, es, hp, hf, hm, hcur, cost, _, run⟩ :=
    field_run_reads hl L m fit (fun _ ↦ True) (L.readable_true m) (headersReads_true headers)
      b j dst hj hd c hc saved cur
  exact ⟨out, es, hp, hf, hm, hcur, cost, run⟩

/-- The remaining fields of one half of the argument packet. -/
def suffix (L : Layout) (mem : Memory w) (b : Bool) (j left : ℕ) :=
  (List.ofFn fun i : Fin left => L.field mem b (j+i.val)).flatten

theorem suffix_succ (L : Layout) (mem : Memory w) (b : Bool) (j left : ℕ) :
    suffix L mem b j (left+1) = L.field mem b j ++ suffix L mem b (j+1) left := by
  simp only [suffix,List.ofFn_succ,Fin.val_zero,Nat.add_zero,List.flatten_cons,Fin.val_succ]
  congr 3
  funext i
  rw [show j+(i.val+1) = j+1+i.val by omega]

theorem suffix_full (L : Layout) (mem : Memory w) (b : Bool) :
    suffix L mem b 0 L.degree = (L.fields mem b).flatten := by simp [suffix,Layout.fields]

theorem scan_run_reads (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (P : ℕ → Prop) (readable : L.Readable m P) (headers : HeadersReads P L M m pc reg)
    (b : Bool) (left j dst : ℕ) (lastSlot : j+left=L.degree)
    (hd : dst+(suffix L m b j left).length < 2^w) (c : Config w p r) (hc : c.pc=pc (.scan b))
    (saved : Saved L reg c) (cur : Cursor L reg c j dst) :
    let words := suffix L m b j left
    ∃ out es, out.pc=(if b then done else pc .reset) ∧ Frame reg c out ∧
      out.privateMem=Layout.placed dst words c.privateMem ∧
      Cursor L reg out L.degree (dst+words.length) ∧
      Cost es ((if b then 11 else 10)*left+5*words.length+1)
        (words.length+(if b then 3 else 2)*left) ∧ Reads P es ∧ Prefix M m c es out := by
  induction left generalizing j dst c with
  | zero =>
    have hj : j=L.degree := by omega
    have eqn : c.reg (reg (tmp 5))=c.reg (reg (tmp 6)) := cur.slot.trans (hj ▸ cur.stop.symm)
    let out := {c with pc := if b then done else pc .reset}
    have ht : Prefix M m c [.tick] out := Prefix.tick (by rw [step_at hl _ hc]; simp [rows,Instr.run,eqn,out])
    have nil : suffix L m b j 0 = [] := by simp [suffix]
    dsimp only
    rw [nil]
    refine ⟨out,[.tick],rfl,⟨rfl,fun _ _ => rfl⟩,?_,?_,by simpa using (Cost.tick (w:=w)),Reads.replicate_tick P 1,ht⟩
    · funext a
      simp [out,Layout.placed]
    · rw [List.length_nil,Nat.add_zero,← hj]
      exact ⟨cur.dest,cur.one,cur.slot,cur.stop,cur.first⟩
  | succ left ih =>
    let tail := suffix L m b (j+1) left
    have len : (suffix L m b j (left+1)).length=L.width m b j+tail.length := by
      rw [suffix_succ,List.length_append,Layout.field_length]
    have headFit : dst+L.width m b j < 2^w := by rw [len] at hd; omega
    obtain ⟨next,hs,hpc,hframe,hpriv,hcur,hcost,hreads,hprefix⟩ := field_run_reads hl L m fit P readable headers b j dst
      (by omega) headFit c hc saved cur
    obtain ⟨out,ts,hend,tframe,tpriv,tcur,tcost,treads,tprefix⟩ :=
      ih (j+1) (dst+L.width m b j) (by omega) (by rw [len] at hd; change _ + tail.length < _; omega)
        next hpc (saved.transport hframe) hcur
    dsimp only
    refine ⟨out,hs++ts,hend,hframe.trans tframe,?_,?_,?_,hreads.append treads,hprefix.trans tprefix⟩
    · rw [tpriv,hpriv,suffix_succ,← Layout.field_length L m b j,Layout.placed_append]
    · rw [len,← Nat.add_assoc]
      exact tcur
    · have h := hcost.append tcost
      change Cost _ _ (L.width m b j+_+(tail.length+_)) at h
      rw [len]
      convert h using 1 <;> dsimp only [tail] <;> cases b <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.mul_add,Nat.mul_one] <;> omega

theorem scan_run (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (headers : Headers L M m pc reg) (b : Bool) (left j dst : ℕ) (lastSlot : j+left=L.degree)
    (hd : dst+(suffix L m b j left).length < 2^w) (c : Config w p r) (hc : c.pc=pc (.scan b))
    (saved : Saved L reg c) (cur : Cursor L reg c j dst) :
    let words := suffix L m b j left
    ∃ out es, out.pc=(if b then done else pc .reset) ∧ Frame reg c out ∧
      out.privateMem=Layout.placed dst words c.privateMem ∧
      Cursor L reg out L.degree (dst+words.length) ∧
      Cost es ((if b then 11 else 10)*left+5*words.length+1)
        (words.length+(if b then 3 else 2)*left) ∧ Prefix M m c es out := by
  obtain ⟨out, es, hp, hf, hm, hcur, cost, _, run⟩ :=
    scan_run_reads hl L m fit (fun _ ↦ True) (L.readable_true m) (headersReads_true headers)
      b left j dst lastSlot hd c hc saved cur
  exact ⟨out, es, hp, hf, hm, hcur, cost, run⟩

/-- The intermediate row returns the slot counter to the site's first slot,
leaving the destination cursor immediately after the outgoing payloads. -/
theorem reset_run (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (c : Config w p r)
    (hc : c.pc=pc .reset) (j dst : ℕ) (cur : Cursor L reg c j dst) :
    ∃ out, out.pc=pc (.scan true) ∧ Frame reg c out ∧ out.privateMem=c.privateMem ∧
      Cursor L reg out 0 dst ∧ Prefix M m c [.tick] out := by
  let out := c.put (pc (.scan true)) (reg (tmp 5)) (c.reg (reg (tmp 7)))
  have keep (i : Fin 9) (h : i≠5) : out.reg (reg (tmp i))=c.reg (reg (tmp i)) :=
    Function.update_of_ne (reg.injective.ne (Sum.inl_injective.ne h)) ..
  refine ⟨out,rfl,⟨rfl,fun i hi => Function.update_of_ne (hi 5).symm ..⟩,rfl,
    ⟨(keep 2 (by decide)).trans cur.dest,(keep 3 (by decide)).trans cur.one,?_,
      (keep 6 (by decide)).trans cur.stop,(keep 7 (by decide)).trans cur.first⟩,
    Prefix.tick (by rw [step_at hl _ hc]; rfl)⟩
  simp only [out,Config.put,Function.update_self,cur.first]

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
