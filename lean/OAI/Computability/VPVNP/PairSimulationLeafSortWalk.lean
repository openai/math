import OAI.Computability.VPVNP.PairSimulationLeafSortFields

/-!
# Executing the complete sorting-field traversal of a virtual RAM leaf

The native scan visits the two fields of each layer in triangular order.
Its private-memory result puts the concatenation of those fields into the
descending part of the incident stack, preserving the resident half buffers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSortFields

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open LeafFieldCopy (word)
open scoped Fin.CommRing

variable {W w D H p r k : ℕ}
variable {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 17 ↪ Fin r} {done : Fin p}

/-- The physical control and counters match a sorting-layer ordinal, or have reached the return. -/
def At (pc : Stage → Fin p) (reg : Fin 17 ↪ Fin r) (done : Fin p) (D i : ℕ)
    (c : Config W p r) : Prop :=
  if h : i < layerCount D then
    let l := (layerEquiv D).symm ⟨i,h⟩
    c.pc = pc .stride ∧ c.reg (reg 13) = word W l.phase ∧ c.reg (reg 14) = word W l.step
  else c.pc = done

private theorem at_layer (l : Layer D) (i : ℕ) (hi : l.ordinal.val = i) (c : Config W p r)
    (hc : c.pc = pc .stride) (hp : c.reg (reg 13) = word W l.phase)
    (ht : c.reg (reg 14) = word W l.step) : At pc reg done D i c := by
  subst i
  have eq : (layerEquiv D).symm l.ordinal = l := (layerEquiv D).symm_apply_apply l
  simpa [At,l.ordinal.isLt,eq] using And.intro hc (And.intro hp ht)

private theorem word_lt_iff {a b : ℕ} (ha : a < 2^W) (hb : b < 2^W) :
    word W a < word W b ↔ a < b := by
  change a % 2^W < b % 2^W ↔ _
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

/-- Number of instructions to advance the triangular pair of counters. -/
def advanceTicks (l : Layer D) := if l.step < l.phase then 3 else if l.phase+1 < D then 5 else 4

/-- Advance from the end of a field pair to the next ordinal or the exit.
The two cases of a triangular row boundary are handled by genuine comparisons. -/
theorem advance_run (hl : Linked M pc reg done) (l : Layer D) (base : LocalPort → ℕ)
    (c : Config W p r) (hc : c.pc = pc .advance) (hf : Fixed reg base D H w c)
    (hD : D < 2^W) (hp : c.reg (reg 13) = word W l.phase)
    (ht : c.reg (reg 14) = word W l.step) (ho : c.reg (reg 6) = word W (arcStart l H w)) :
    ∃ cost ≤ 5, ∃ out, Prefix M c (List.replicate cost .tick) out ∧
      At pc reg done D (l.ordinal.val+1) out ∧
      out.reg (reg 6) = word W (arcStart l H w + blockBits H w) ∧
      out.reg (reg 2) = c.reg (reg 2) ∧ Frame reg c out ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧ cost = advanceTicks l := by
  let a := c.put (pc .stepTest) (reg 6) (word W (arcStart l H w + blockBits H w))
  have s0 : M.program.step c = .localStep a := by
    rw [step_at hl .advance c hc]
    simp [instruction,Instr.run,BinaryOp.eval,ho,hf.len,a,word]
  have f0 : Frame reg c a := frame_put c _ 6 _ (by decide)
  have e : a.reg (reg 14) < a.reg (reg 13) ↔ l.step < l.phase := by
    simpa [a,Config.put,ht,hp] using (word_lt_iff (W := W) (l.step_le.trans_lt (l.phase_lt.trans hD))
      (l.phase_lt.trans hD))
  by_cases more : l.step < l.phase
  · let b := {a with pc := pc .nextStep}
    let out := b.put (pc .stride) (reg 14) (word W (l.step+1))
    have s1 : M.program.step a = .localStep b := by
      rw [step_at hl .stepTest a rfl]
      simp [instruction,Instr.run,b,e,more]
    have s2 : M.program.step b = .localStep out := by
      rw [step_at hl .nextStep b rfl]
      simp [instruction,Instr.run,BinaryOp.eval,b,a,out,Config.put,ht,hf.one,word]
    let next : Layer D := ⟨l.phase,l.step+1,l.phase_lt,more⟩
    refine ⟨3, by decide, out, .tick s0 (.tick s1 (.tick s2 (.nil _))), ?_, ?_, ?_,
      f0.trans (frame_put b _ 14 _ (by decide)), rfl,rfl,by simp [advanceTicks,more]⟩
    · exact at_layer next _ (by simp [next,Layer.ordinal,Nat.add_assoc]) _ rfl
        (by simp [out,b,a,Config.put,next,hp]) (Config.put_same ..)
    · simp [out,b,a,Config.put]
    · simp [out,b,a,Config.put]
  · let b := {a with pc := pc .nextPhase}
    let d := b.put (pc .phaseTest) (reg 13) (word W (l.phase+1))
    have s1 : M.program.step a = .localStep b := by
      rw [step_at hl .stepTest a rfl]
      simp [instruction,Instr.run,b,e,more]
    have s2 : M.program.step b = .localStep d := by
      rw [step_at hl .nextPhase b rfl]
      simp [instruction,Instr.run,BinaryOp.eval,b,a,d,Config.put,hp,hf.one,word]
    have f2 : Frame reg c d := f0.trans (frame_put b _ 13 _ (by decide))
    have h := l.phase_lt
    have hrow : l.step = l.phase := le_antisymm l.step_le (by omega)
    have eq : l.ordinal.val+1 = layerCount (l.phase+1) := by
      rw [PrimedInputRAM.PortCode.layerCount_next]
      change layerCount l.phase + l.step + 1 = _
      omega
    have e' : d.reg (reg 13) < d.reg (reg 11) ↔ l.phase+1 < D := by
      simpa [d,b,a,Config.put,hf.dims] using (word_lt_iff (W := W) (by omega : l.phase+1 < 2^W) hD)
    by_cases live : l.phase+1 < D
    · let f := {d with pc := pc .resetStep}
      let out := f.put (pc .stride) (reg 14) 0
      have s3 : M.program.step d = .localStep f := by
        rw [step_at hl .phaseTest d rfl]
        simp [instruction,Instr.run,f,e',live]
      have s4 : M.program.step f = .localStep out := step_at hl .resetStep f rfl
      let next : Layer D := ⟨l.phase+1,0,live,by omega⟩
      refine ⟨5, le_rfl, out,.tick s0 (.tick s1 (.tick s2 (.tick s3 (.tick s4 (.nil _))))),
        ?_, ?_, ?_, f2.trans (frame_put f _ 14 _ (by decide)),rfl,rfl,by simp [advanceTicks,more,live]⟩
      · exact at_layer next _ (by simpa [next,Layer.ordinal] using eq.symm) _ rfl
          (by simp [out,f,d,Config.put,next]) (Config.put_same ..)
      · simp [out,f,d,b,a,Config.put]
      · simp [out,f,d,b,a,Config.put]
    · let out := {d with pc := done}
      have s3 : M.program.step d = .localStep out := by
        rw [step_at hl .phaseTest d rfl]
        simp [instruction,Instr.run,out,e',live]
      have last : l.ordinal.val+1 = layerCount D := by rw [eq, show l.phase+1 = D by omega]
      refine ⟨4,by decide,out,.tick s0 (.tick s1 (.tick s2 (.tick s3 (.nil _)))),
        by simp [At,last,out], ?_, ?_,f2,rfl,rfl,by simp [advanceTicks,more,live]⟩
      · simp [out,d,b,a,Config.put]
      · simp [out,d,b,a,Config.put]

/-- Logical stream of a consecutive interval of layer ordinals. -/
def stream (buf : Buffers D H w) (i n : ℕ) (fits : i+n ≤ layerCount D) : List Bool :=
  (List.ofFn fun j : Fin n => block ((layerEquiv D).symm ⟨i+j.val, by have := j.isLt; omega⟩) buf).flatten

private theorem stream_succ (buf : Buffers D H w) (i n : ℕ) (fits : i+(n+1) ≤ layerCount D) :
    stream buf i (n+1) fits =
      block ((layerEquiv D).symm ⟨i,by omega⟩) buf ++ stream buf (i+1) n (by omega) := by
  simp only [stream,List.ofFn_succ,List.flatten_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ]
  congr 2
  apply congrArg List.ofFn
  funext j
  simp [Nat.add_assoc,Nat.add_comm 1]

@[simp] theorem stream_length (buf : Buffers D H w) (i n : ℕ) (fits) :
    (stream buf i n fits).length = n*(2*blockBits H w) := by
  induction n generalizing i with
  | zero => simp [stream]
  | succ n ih => rw [stream_succ,List.length_append,block_length,ih]; ring

/-- Total number of native instructions for the indicated consecutive sorting layers. -/
def streamTicks (D H w i n : ℕ) (fits : i+n ≤ layerCount D) : ℕ :=
  (List.ofFn fun j : Fin n =>
    10*blockBits H w+9+advanceTicks ((layerEquiv D).symm ⟨i+j.val, by have := j.isLt; omega⟩)).sum

private theorem streamTicks_succ (D H w i n : ℕ) (fits : i+(n+1) ≤ layerCount D) :
    streamTicks D H w i (n+1) fits =
      10*blockBits H w+9+advanceTicks ((layerEquiv D).symm ⟨i,by omega⟩) +
        streamTicks D H w (i+1) n (by omega) := by
  simp [streamTicks,List.ofFn_succ,Nat.add_assoc,Nat.add_comm 1]

private theorem walk (hl : Linked M pc reg done) (base : LocalPort → ℕ) (buf : Buffers D H w)
    (lo i n : ℕ) (finish : i+n = layerCount D) (c : Config W p r) (hc : At pc reg done D i c)
    (hf : Fixed reg base D H w c) (hD : D < 2^W)
    (ho : c.reg (reg 6) = word W (D*(8*w)+i*blockBits H w))
    (hd : c.reg (reg 2) = word W (lo+n*(2*blockBits H w))) (hs : LeafIncidentLoad.Stored base buf c.privateMem)
    (fit : lo+n*(2*blockBits H w) < 2^W) (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (sep : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+n*(2*blockBits H w) ≤ base a) :
    ∃ t ≤ n*(10*blockBits H w+14), ∃ out, Prefix M c (List.replicate t .tick) out ∧
      out.pc = done ∧ out.reg (reg 2) = word W lo ∧ Frame reg c out ∧
      out.privateMem = LeafFieldCopy.place lo (stream buf i n finish.le) c.privateMem ∧ out.persistent = c.persistent ∧
      t = streamTicks D H w i n finish.le := by
  induction n generalizing i c with
  | zero =>
    have hi : i = layerCount D := by omega
    exact ⟨0, by simp, c, .nil _, by simpa [At,hi] using hc, by simpa using hd,
      fun _ _ => rfl, by simp [stream,LeafFieldCopy.place], rfl, by simp [streamTicks]⟩
  | succ n ih =>
    let B := blockBits H w
    let l := (layerEquiv D).symm ⟨i, by omega⟩
    have ord : l.ordinal.val = i := congrArg Fin.val ((layerEquiv D).apply_symm_apply ⟨i,by omega⟩)
    have ha : c.pc = pc .stride ∧ c.reg (reg 13) = word W l.phase ∧ c.reg (reg 14) = word W l.step := by
      simpa [At,show i < layerCount D by omega,l] using hc
    let lower := lo+n*(2*B)
    have hlen : lower + 2*blockBits H w = lo+(n+1)*(2*blockBits H w) := by dsimp [lower,B]; ring
    have hlow : lo ≤ lower := Nat.le_add_right ..
    have hprefix := layer_run hl l base buf lower c ha.1 hf hD ha.2.1 ha.2.2
      (by simpa [arcStart,ord] using ho) (hlen ▸ hd) hs (hlen ▸ fit) sourceFit
      (fun a => by have := sep a; omega)
    obtain ⟨u,pre,up,ud,uo,uph,ust,fu,um,uper⟩ := hprefix
    obtain ⟨cost,bound,v,adv,va,vo,vd,fv,vm,vper,vticks⟩ := advance_run hl l base u up (hf.of_frame fu) hD
      (uph.trans ha.2.1) (ust.trans ha.2.2) (by simpa [uo,arcStart,ord] using ho)
    have hstore : LeafIncidentLoad.Stored base buf v.privateMem := by
      rw [vm,um]
      exact stored_place _ _ _ _ _ hs (by rw [block_length,hlen]; exact fit.le) sourceFit
        (fun a => by rw [block_length,hlen]; have := sep a; omega)
    have vOff : v.reg (reg 6) = word W (D*(8*w)+(i+1)*blockBits H w) := by
      rw [vo,arcStart,ord]
      congr 1; ring
    have same : i+1+n = layerCount D := by omega
    have hrest := Nat.add_le_add_left (Nat.mul_le_mul_right (2*blockBits H w) (Nat.le_succ n)) lo
    obtain ⟨cost',bound',out,tail,hpc,hcur,ff,hm,hper,hticks⟩ := ih (i+1) same v (ord ▸ va)
      (hf.of_frame (fu.trans fv)) vOff (vd.trans ud) hstore (hrest.trans_lt fit)
      (fun a => (sep a).imp_right hrest.trans)
    refine ⟨(10*B+9)+cost+cost', ?_,out, ?_,hpc,hcur,(fu.trans fv).trans ff, ?_,hper.trans (vper.trans uper), ?_⟩
    · have eq : (n+1)*(10*B+14) = n*(10*B+14)+(10*B+14) := by ring
      dsimp only [B] at eq ⊢
      omega
    · simpa only [List.replicate_add,B,List.append_assoc] using pre.append (adv.append tail)
    · rw [hm,vm,um,stream_succ,LeafIncidentLoad.place_append,stream_length]
    · rw [vticks,hticks,streamTicks_succ]

/-- The full finite-control triangular scan on four resident half buffers. -/
theorem sort_run (hl : Linked M pc reg done) (base : LocalPort → ℕ) (buf : Buffers D H w)
    (lo : ℕ) (c : Config W p r) (hc : c.pc = pc .resetPhase) (hf : Fixed reg base D H w c)
    (hpos : 0 < D) (hD : D < 2^W) (ho : c.reg (reg 6) = word W (D*(8*w)))
    (hd : c.reg (reg 2) = word W (lo+layerCount D*(2*blockBits H w)))
    (hs : LeafIncidentLoad.Stored base buf c.privateMem) (fit : lo+layerCount D*(2*blockBits H w) < 2^W)
    (sourceFit : ∀ a, base a+ramPayloadWidth D H w ≤ 2^W)
    (sep : ∀ a, base a+ramPayloadWidth D H w ≤ lo ∨ lo+layerCount D*(2*blockBits H w) ≤ base a) :
    ∃ t ≤ 3+layerCount D*(10*blockBits H w+14), ∃ out, Prefix M c (List.replicate t .tick) out ∧
      out.pc = done ∧ out.reg (reg 2) = word W lo ∧ Frame reg c out ∧
      out.privateMem = LeafFieldCopy.place lo (stream buf 0 (layerCount D) (by simp)) c.privateMem ∧
      out.persistent = c.persistent ∧ t = 3+streamTicks D H w 0 (layerCount D) (by simp) := by
  let a := c.put (pc .phaseTest) (reg 13) 0
  let b := {a with pc := pc .resetStep}
  let d := b.put (pc .stride) (reg 14) 0
  have s0 : M.program.step c = .localStep a := step_at hl _ c hc
  have s1 : M.program.step a = .localStep b := by
    rw [step_at hl .phaseTest a rfl]
    have test : a.reg (reg 13) < a.reg (reg 11) := by
      simpa [a,Config.put,hf.dims] using (word_lt_iff (Nat.two_pow_pos W) hD).mpr hpos
    simp [instruction,Instr.run,b,test]
  have s2 : M.program.step b = .localStep d := step_at hl .resetStep b rfl
  have fd : Frame reg c d := (frame_put c _ 13 _ (by decide)).trans (frame_put b _ 14 _ (by decide))
  let first : Layer D := ⟨0,0,hpos,le_rfl⟩
  have at0 : At pc reg done D 0 d := at_layer first 0 rfl d rfl
    (by simp [first,d,b,a,Config.put]) (Config.put_same ..)
  obtain ⟨t,ht,out,run,exit,cur,frame,hm,per,exactTicks⟩ := walk hl base buf lo 0 (layerCount D) (by simp) d at0
    (hf.of_frame fd) hD (by simpa [d,b,a,Config.put] using ho) (by simpa [d,b,a,Config.put] using hd)
    hs fit sourceFit sep
  have start : Prefix M c (List.replicate 3 .tick) d := .tick s0 (.tick s1 (.tick s2 (.nil _)))
  exact ⟨3+t,by omega,out,by simpa only [List.replicate_add] using start.append run,
    exit,cur,fd.trans frame,hm,per,congrArg (3+·) exactTicks⟩

end PairSimulation.LeafSortFields

end VPVNP
end Computability
end OAI
