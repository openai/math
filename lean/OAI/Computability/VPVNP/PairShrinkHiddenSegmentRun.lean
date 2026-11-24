import OAI.Computability.VPVNP.PairShrinkHiddenSegment

/-! # Header and field execution in the hosted hidden segment -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess.Table

open BurstRAM PrivateRAM CompressorRecords NodeArguments.ChildScan
open scoped Fin.CommRing

variable {s t p r W : ℕ}

set_option maxHeartbeats 600000 in
/-- The live header sets up the hidden loop without changing any private
memory cell or register outside the installed header bank. -/
theorem segment_prepare_raw (M : Machine W p r 11) (pc : Fin (segmentCount s t) → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
    (prv : Fin (R s t) ↪ Fin r) (ret : Fin p)
    (rows : ∀ i, M.code (pc i) = ((segment s t).row pc dfs saved prv ret i).resize W)
    (g : Args W) (m : Memory W) (oldLevel : ℕ) (c : Config W p r)
    (entry : c.pc = pc (segment s t).entry) (op : SegmentOperands s t prv g oldLevel c)
    (selectors : g.selectorBits = (s : Word W)) (stride : g.rowStride = t)
    (fits : oldLevel+38 < 2^W) (published : Header.Published g oldLevel m) :
    let ev := Header.trace s t ((segmentInputs s t).trans prv) ((vm s t).trans prv) c m
    ∃ d, Prefix M m c d [] ev ∧ d.pc = segmentLoop s t pc (.inl .one) ∧
      Inputs g ((regs s t).trans prv) d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range ((vm s t).trans prv) → d.reg i = c.reg i) ∧
      ev.length = (lines s t).length ∧ countProbes ev = 5 ∧ choiceBits ev = [] := by
  obtain ⟨header,_⟩ : RegisterSetup.Linked ((vm s t).trans prv) ((segmentInputs s t).trans prv) M
      (segmentHeader s t pc) (lines s t) ∧ _ := segment_linked s t M pc dfs saved prv ret rows
  let H := segmentHeader s t pc
  let I := (segmentInputs s t).trans prv
  let V := (vm s t).trans prv
  let G := (regs s t).trans prv
  have free (i : Fin (aux s t)) (j : Fin 6) : V i ≠ I j := prv.injective.ne (safe s t i j)
  have out (i : Fin 10) : V (RegisterSetup.output (Header.recipe s t) i) = G (Header.target i) :=
    by simp only [V,G,Function.Embedding.trans_apply,outputs s t i]
  have atStart : c.pc = H 0 := entry.trans (segment_entry s t pc)
  have lev : c.reg (I 5) = (oldLevel : Word W) := op.level
  have own : c.reg (I 0) = (g.owner : Word W) := op.owner
  have base : c.reg (I 1) = (g.scratchBase : Word W) := op.base
  have size : c.reg (I 2) = (g.slotStride : Word W) := op.stride
  have run := @Header.raw_run W p r 11 M g m oldLevel s t selectors stride I H G V
    header free out c atStart lev own base size fits published
  obtain ⟨d,path,len,probes,bits,ep,ready,priv,pers,keep⟩ := run
  exact ⟨d,path,ep.trans (segment_after_header s t pc),ready,priv,pers,
    fun i f => keep i (fun j eq => f ⟨j,eq.symm⟩),len,probes,bits⟩

/-- A full hosted scan on a valid row, returning to the caller's exact PC.
Registers outside its private bank remain available to the next segment. -/
theorem segment_run (M : Machine W p r 11) (pc : Fin (segmentCount s t) → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (prv : Fin (R s t) ↪ Fin r) (ret : Fin p)
    (code : ∀ i, M.code (pc i) = ((segment s t).row pc dfs saved prv ret i).resize W)
    (g : Args W) (m : Memory W) (oldLevel : ℕ) (c : Config W p r) (es : List Row)
    (entry : c.pc = pc (segment s t).entry) (op : SegmentOperands s t prv g oldLevel c)
    (selectors : g.selectorBits = (s : Word W)) (stride : g.rowStride = t)
    (fits : oldLevel+38 < 2^W) (published : Header.Published g oldLevel m)
    (fit : g.countBase+g.owner < 2^W) (count : (m (g.countBase+g.owner)).val = es.length)
    (valid : ValidRows g m es) :
    let head := Header.trace s t ((segmentInputs s t).trans prv) ((vm s t).trans prv) c m
    let ev := head ++ events g m es
    ∃ d, Prefix M m c d (stream es) ev ∧ d.pc = ret ∧
      d.privateMem = storeRows g.scratchBase g.slotStride es c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range prv → d.reg i = c.reg i) ∧
      ev.length = (lines s t).length+7+25*es.length+6*(stream es).length ∧
      countProbes ev = 6+3*es.length ∧ choiceBits ev = stream es ∧
      ∀ bs, bs.length < (stream es).length → ¬ DFS.Returns M c m bs := by
  intro head ev
  obtain ⟨a,pref,ep,ready,pm,ps,frame,len,probes,choices⟩ :=
    segment_prepare_raw M pc dfs saved prv ret code g m oldLevel c entry op selectors stride fits published
  have link := (segment_linked s t M pc dfs saved prv ret code).2
  obtain ⟨d,path,endPC,keep,priv,pers⟩ := native link g m es a ep ready fit count valid
  obtain ⟨work,reads,bits⟩ := cost g m es
  refine ⟨d,pref.trans path,endPC,priv.trans (congrArg _ pm),pers.trans ps,?_,?_,?_,?_,?_⟩
  · intro i free
    have sep (j : Fin 22) : i ≠ prv (regs s t j) := fun eq => free ⟨_,eq.symm⟩
    exact (keep i (sep 3) (sep 21) (fun j _ => sep j)).trans (frame i fun ⟨j,eq⟩ => free ⟨_,eq⟩)
  · simp only [ev,List.length_append]
    change head.length = _ at len
    omega
  · simp only [ev,countProbes_append]
    change countProbes head = 5 at probes
    omega
  · simp only [ev,PrimedInputRAM.Flow.choiceBits_append]
    change choiceBits head = [] at choices
    rw [choices,bits,List.nil_append]
  · intro bs short
    exact mt (pref.returns bs).mp (native_short link g m es a ep ready fit count valid bs short)

end PairSimulation.ShrinkHiddenGuess.Table

end VPVNP
end Computability
end OAI
