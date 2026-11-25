import OAI.Optimization.LinearProgramming.Recovery.PairBuilderIO

/-! Relocate the matrix ROMs on finite native banks and export each actual dense table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Block RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

variable {K : Type}
variable {h n k s a b : ℕ} {l : Layout h n} {m t : Memory K}

structure Passive (m t : Memory K) : Prop where
  data : t.data=m.data
  held : ∀i,Held i→t.index i=m.index i

structure Copied (m t : Memory K) (dst count : ℕ) : Prop where
  data : ∀p,p≠4→(p<dst ∨ dst+count ≤ p)→t.data p=m.data p
  held : ∀i,Held i→t.index i=m.index i

theorem held_ne {p j : ℕ} (hp : Held p) (hj : j=1 ∨ j=180 ∨ j=181 ∨ j=183 ∨ j=206 ∨ j=207) : p≠j := by
  rcases hp with h|h|h|h <;> rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem Passive.refl (m : Memory K) : Passive m m := ⟨rfl,fun _ _=>rfl⟩

theorem Passive.index (m : Memory K) (i j : ℕ) (ok : i=1 ∨ i=180 ∨ i=181 ∨ i=183 ∨ i=206 ∨ i=207) : Passive m (m.putIndex i j) :=
  ⟨rfl,fun _ hp=>Memory.putIndex_ne m (held_ne hp ok) j⟩

theorem Passive.trans {u v w : Memory K} (uv : Passive u v) (vw : Passive v w) : Passive u w := ⟨vw.data.trans uv.data,fun i hi=>(vw.held i hi).trans (uv.held i hi)⟩
theorem MetaEffect.passive {p : Phase} (q : MetaEffect p m t) : Passive m t := ⟨q.data,q.held⟩

theorem Passive.copied {u v w : Memory K} {dst count : ℕ} (uv : Passive u v) (vw : Copied v w dst count) : Copied u w dst count :=
  ⟨fun p hp bound=>(vw.data p hp bound).trans (congrFun uv.data p), fun i hi=>(vw.held i hi).trans (uv.held i hi)⟩

theorem Copied.table {u v : Memory K} {dst count p nr nc : ℕ} (uv : Copied u v dst count)
    (start : 5 ≤ p) (away : p+nr*nc ≤ dst ∨ dst+count ≤ p) : uniformRect nr nc p v=uniformRect nr nc p u := by
  ext i j; apply uv.data
  · omega
  · have hit:=rectOffset_lt i j; omega

noncomputable def callCost {h n : ℕ} (l : Layout h n) := metaBudget.eval (limit l)+(19*capacity h n l.previous+225+(2*workerTime h n+2))

/-- A normal-entry worker produces precisely the specified new native memory, preserving
all logical scalar registers and the protected LP pointers. The reusable window is strict. -/
theorem loaded_call [Field K] [LinearOrder K] [IsStrictOrderedRing K] (port : InPort) (code : Block) (native caller after : Memory K) (P Q : K→Prop)
    (v : Internal l k s a b caller) (D : Matrix (Fin (port.rows h n k)) (Fin n) K)
    (table : uniformRect (port.rows h n k) n (port.source l a) caller=D) (old : ℕ)
    (foot : Footprint old (native.atPC 0)) (room : old < capacity h n l.previous)
    (hn : native.AllData P) (hc : caller.AllData P) (zero : P 0) (wide : ∀x,Q x→P x)
    (addr : addressBudget (code.compile 0++[.halt 0]) ≤ codeReserve) {c : ℕ}
    (clock : c+1 ≤ workerTime h n) (work : Eval (Memory.AllData Q) code (start [port.rows h n k,n] (encodedGramInput D)).memory c after) :
    ∃t,((«meta» port.phase).seq (normalCall code)).Run P (Odd.memory native caller) (callCost l) (Odd.memory after t) ∧
      t.AllData P ∧ after.AllData P ∧ Internal l k s a b t ∧ Passive caller t ∧
      Footprint (capacity h n l.previous-1) (after.atPC 0) := by
  obtain ⟨x,stage,sx,q⟩:=v.metaRun port.phase native P hn hc
  have px:=load_raw port v q D table
  have rows : port.rows h n k ≤ h+n := by cases port <;> simp only [InPort.rows] <;> have hh:=v.firstFits <;> omega
  obtain ⟨call,next⟩:=normalCall_run D code native x P Q _ 208 _ old px foot room (input_fits _ rows) (pair_fits ..) hn sx zero wide work
  have quiet : Quiet port.phase := by cases port <;> trivial
  refine ⟨x.putIndex 1 0,(stage.seq call).mono ?_,sx,fun j=>wide _ (work.safe_end j),(q.quiet quiet v).tagged,
    q.passive.trans (Passive.index _ 1 0 (Or.inl rfl)),next.mono ?_⟩
  · unfold callCost; omega
  · have inside:=output_fits l.previous rows _ addr clock D; omega

/-- The actual odd-bank export writes every row-major coordinate of the native matrix. -/
theorem copy_table [Field K] [LinearOrder K] [IsStrictOrderedRing K] (native caller : Memory K) (P : K→Prop) (v : Internal l k s a b caller) (hn : native.AllData P) (hc : caller.AllData P)
    (r src dst : ℕ) (pr : caller.index 180=src) (pd : caller.index 181=dst) (pn : caller.index 182=r*n) (hd : 5 ≤ dst) :
    ∃t,copyRows.Run P (Odd.memory native caller) (21*(r*n)+5) (Odd.memory native t) ∧ t.AllData P ∧ Internal l k s a b t ∧
      uniformRect r n dst t=uniformRect r n src native ∧ Copied caller t dst (r*n) := by
  obtain ⟨t,c,time,run,words,frame,_,_,_,index⟩:=BankRead.copyWindow_eval P native caller hn hc _ _ _ pr pd pn hd
  refine ⟨t,(Fragment.Run.ofBlock run).mono time,fun j=>by simpa using run.safe_end (Odd.slot j),v.traced index,?_,frame,?_⟩
  · ext i j; simpa only [uniformRect,Nat.add_assoc] using words (i.val*n+j.val) (rectOffset_lt i j)
  · intro j hj
    exact index j (held_ne hj (Or.inr (Or.inl rfl))) (held_ne hj (Or.inr (Or.inr (Or.inl rfl)))) (held_ne hj (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
