import OAI.Computability.BorderVNP.PackedReportWriter
import OAI.Computability.BorderVNP.DiagonalTallyRAMTrace

/-! # Exact execution of the supplemental report-row writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.Writer

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM CellSparse
open private push_eval push_safe from OAI.Computability.BorderVNP.PackedReportWriter

/-- The input count and relative lane words actually read from the decoded sidecar. -/
def Frame.input (f : Frame) (n : ℕ) (rel : ℕ → ℕ) (m : ℕ → ℕ) : Prop :=
  m f.side = n ∧ ∀ i < n, m (f.side+3*(i+1)) = rel i

private structure Scan (f : Frame) (m₀ : ℕ → ℕ) (rel : ℕ → ℕ) (n i : ℕ) (z : NatState) : Prop where
  fixed : f.static z
  useLane : z.reg 24 = f.useStart+i*f.copies
  output : z.reg 28 = f.dst+9*i
  recordCount : z.reg 29 = f.previousRows+i
  index : z.reg 40 = i
  bound : z.reg 41 = n
  one : z.reg 42 = 1
  zero : z.reg 43 = 0
  three : z.reg 44 = 3
  image : z.mem = write m₀ f.dst ((f.rows rel i).flatMap Packet.record)

private theorem initial (pub : Arg → ℕ) (f : Frame) (w n : ℕ) (rel : ℕ → ℕ)
    (fit : f.Fits w n rel) (z : NatState) (loaded : f.loaded z) (supplied : f.input n rel z.mem) :
    setup.fixedSafe w pub z ∧ Scan f z.mem rel n 0 (setup.fixedEval pub z) := by
  obtain ⟨⟨h19,h20,h21,h25,h26,h27⟩,h24,h28,h29⟩ := loaded
  have hd := fit.dst_end
  have hn := supplied.1
  have hw : w ≠ 0 := by rintro rfl; simp at hd
  constructor
  · simp [setup,Code.block,Code.fixedSafe,Code.safeReadOnly,hw]; omega
  · constructor <;>
      simp [Frame.static,setup,Code.block,Code.fixedEval,Code.evalNat,Function.update,
        h19,h20,h21,h25,h26,h27,h24,h28,h29,hn,Frame.rows,write]

private theorem iteration (pub : Arg → ℕ) (f : Frame) (w n : ℕ) (m₀ rel : ℕ → ℕ)
    (fit : f.Fits w n rel) (supplied : f.input n rel m₀) (i : ℕ) (hi : i < n)
    (z : NatState) (h : Scan f m₀ rel n i z) :
    body.fixedSafe w pub z ∧ Scan f m₀ rel n (i+1) (body.fixedEval pub z) := by
  obtain ⟨h19,h20,h21,h25,h26,h27⟩ := h.fixed
  have hsep : f.side+3*(i+1) < f.dst ∨
      f.dst+((f.rows rel i).flatMap Packet.record).length ≤ f.side+3*(i+1) := by
    rw [f.rows_words_length]
    rcases fit.disjoint with hdis | hdis <;> omega
  have hread : z.mem (f.side+3*(i+1)) = rel i := by
    rw [h.image,write_outside _ _ _ _ hsep]
    exact supplied.2 i hi
  have haddr := fit.side_end
  have hrow := fit.row_base i hi
  have hout := fit.dst_end
  have hcnt := fit.count_end
  have huse := fit.use_end
  have hmul : (i+1)*f.copies ≤ n*f.copies := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at hmul
  let a := readLane.fixedEval pub z
  have ar : a.reg = Function.update (Function.update z.reg 45 (f.side+3*(i+1))) 46 (f.base+rel i) := by
    simp [a,readLane,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update_idem,
      h.index,h.one,h.three,h20,h25,Nat.mul_comm (i+1) 3,hread]
  have am : a.mem = z.mem := rfl
  have au : a.reg 42 = 1 := by simp [ar,h.one]
  have ao : a.reg 28 = f.dst+9*i := by simp [ar,h.output]
  have aw : equalRegs.map a.reg = Packet.record (f.equalRow i (rel i)) := by
    simp [equalRegs,ar,h21,h26,h.one,h.useLane,Frame.equalRow,Packet.record,Packet.port,stagedPort,usePort]
  let b := (push equalRegs).fixedEval pub a
  have be : b = ⟨Function.update a.reg 28 (f.dst+9*i+9),
      write z.mem (f.dst+9*i) (Packet.record (f.equalRow i (rel i)))⟩ := by
    rw [show b = _ from push_eval pub a equalRegs au (by decide),aw,am,ao]
    rfl
  constructor
  · change readLane.fixedSafe w pub z ∧ (push equalRegs).fixedSafe w pub a ∧ advance.fixedSafe w pub b
    refine ⟨?_,push_safe pub w a equalRegs au (by rw [ao]; change _+9 < _; omega),?_⟩
    · simp [readLane,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,
        addressOp,Function.update,h.index,h.one,h.three,h20,h25,Nat.mul_comm (i+1) 3,hread]
      omega
    · simp [advance,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,
        addressOp,Function.update,be,ar,h.useLane,h21,h.recordCount,h.one,h.index]
      omega
  · change Scan f m₀ rel n (i+1) (advance.fixedEval pub b)
    constructor <;>
      simp [advance,Code.block,Code.fixedEval,Code.evalNat,addressOp,be,ar,Function.update,
        Frame.static,h19,h20,h21,h25,h26,h27,h.useLane,h.recordCount,h.index,h.bound,h.one,h.zero,
        h.three,Frame.rows,List.flatMap_append,write_append,f.rows_words_length,h.image,
        Nat.succ_mul,Nat.add_assoc]
    omega

/-- Observable registers and memory after writing the whole packet. -/
structure Frame.Result (f : Frame) (n : ℕ) (rel m₀ : ℕ → ℕ) (z : NatState) : Prop where
  /-- The use cursor advances by the number of sources times the bundle multiplicity. -/
  useLane : z.reg 24 = f.useStart+n*f.copies
  /-- Nine words per equality and six for the final zero record. -/
  output : z.reg 28 = f.dst+9*n+6
  /-- One binding for each listed position and one for the unused suffix. -/
  count : z.reg 29 = f.previousRows+n+1
  /-- The entire resulting word memory, including all addresses outside the packet. -/
  image : z.mem = write m₀ f.dst (((f.rows rel n)++[f.zeroRow n]).flatMap Packet.record)

private theorem finalStep (pub : Arg → ℕ) (f : Frame) (w n : ℕ) (m₀ rel : ℕ → ℕ)
    (fit : f.Fits w n rel) (z : NatState) (h : Scan f m₀ rel n n z) :
    finish.fixedSafe w pub z ∧ f.Result n rel m₀ (finish.fixedEval pub z) := by
  obtain ⟨h19,_,h21,h25,h26,h27⟩ := h.fixed
  let a := tailLane.fixedEval pub z
  have ar : a.reg = Function.update (Function.update z.reg 47 (f.cap-n)) 46 (f.base+(f.orig+n)) := by
    simp [a,tailLane,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update_idem,
      h19,h25,h27,h.bound]
  have am : a.mem = z.mem := rfl
  have au : a.reg 42 = 1 := by simp [ar,h.one]
  have ao : a.reg 28 = f.dst+9*n := by simp [ar,h.output]
  have aw : zeroRegs.map a.reg = Packet.record (f.zeroRow n) := by
    simp [zeroRegs,ar,h21,h26,h.zero,h.one,Frame.zeroRow,Packet.record,Packet.port,stagedPort]
  let b := (push zeroRegs).fixedEval pub a
  have be : b = ⟨Function.update a.reg 28 (f.dst+9*n+6),write z.mem (f.dst+9*n) (Packet.record (f.zeroRow n))⟩ := by
    rw [show b = _ from push_eval pub a zeroRegs au (by decide),aw,am,ao]
    rfl
  constructor
  · change tailLane.fixedSafe w pub z ∧ (push zeroRegs).fixedSafe w pub a ∧
      (Code.binary .add 29 29 42).fixedSafe w pub b
    refine ⟨?_,push_safe pub w a zeroRegs au (by rw [ao]; exact fit.dst_end),?_⟩
    · have hpad := fit.padding_base
      simp [tailLane,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,
        addressOp,Function.update,h19,h25,h27,h.bound,fit.count_le]; omega
    · simpa [Code.fixedSafe,Code.safeReadOnly,addressOpFits,be,ar,h.recordCount,h.one] using fit.count_end
  · change f.Result n rel m₀ ((Code.binary .add 29 29 42).fixedEval pub b)
    constructor <;> simp [Code.fixedEval,Code.evalNat,addressOp,Function.update,be,ar,h.useLane,
      h.recordCount,h.one,h.image,write_append,f.rows_words_length]

/-- Real word-machine run of the fixed writer, including the exact memory image
and cursor changes. The cost includes all probes, loop guards and the empty-source case. -/
theorem program_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : Frame) (n : ℕ) (rel : ℕ → ℕ)
    (loaded : f.loaded (.ofWords s m)) (fit : f.Fits w n rel) (supplied : f.input n rel (readings m)) :
    BoundedRun pub mac program s m (28*n+23) (f.Result n rel (readings m)) := by
  obtain ⟨hs,init⟩ := initial (readings pub) f w n rel fit (.ofWords s m) loaded supplied
  have run := (setup.runFixed pub mac s m hs).seq (fun u mu hu => by
    have h₀ : Scan f (readings m) rel n 0 (.ofWords u mu) := hu ▸ init
    have loop := run_counted_loop pub mac 40 41 body n body.slots (Scan f (readings m) rel n)
      (fun _ _ h => ⟨h.index,h.bound⟩) (fun i hi s' m' h => by
        obtain ⟨ha,hb⟩ := iteration (readings pub) f w n (readings m) rel fit supplied i hi (.ofWords s' m') h
        exact (body.runFixed pub mac s' m' ha).mono le_rfl (fun _ he => he ▸ hb))
      0 (Nat.zero_le _) u mu h₀
    exact loop.seq (fun v mv hv => by
      obtain ⟨ha,hb⟩ := finalStep (readings pub) f w n (readings m) rel fit (.ofWords v mv) hv
      exact (finish.runFixed pub mac v mv ha).mono le_rfl (fun _ he => he ▸ hb)))
  exact run.mono (by change 5+((n-0)*(27+1)+1+17) ≤ _; omega) (fun _ h => h)

/-- The native table has no private choices, signed corrections or burst charges. -/
theorem program_ordinary {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (h : Runs pub mac program s m es t mt) :
    ∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0 :=
  DiagonalTallyRAM.ordinary_run (by decide) h

end Packing.BottomReports.Writer

end BorderVNP
end Computability
end OAI
