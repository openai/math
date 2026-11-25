import OAI.Optimization.LinearProgramming.Compression.CallableCapacityTerm
import OAI.Optimization.LinearProgramming.Compression.SymbolicWorkspaceAddress
import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryTime
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup
import OAI.Optimization.LinearProgramming.RAM.RAMFrame

/-! Fixed address code installing the capacity, incoming row, and first free
work cell of the numerical comparator from the six live cache headers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable RAM.Tape MinorProxyCache PrimalDual Polynomial

def initialResidentRow (L : Buffers) (d : ℕ) : ℕ :=
  128+L.magBase+L.gridBase+L.scalePtr+L.flagBase+d

private def bindings : List CursorBind :=
  [.reg 0 83,.reg 1 84,.reg 2 86,.reg 3 82,.reg 4 80,.reg 5 81]

private def inputs (m : Memory ℚ) : Fin 6 → ℕ :=
  ![m.index 83,m.index 84,m.index 86,m.index 82,m.index 80,m.index 81]

def initialResidentCapacityTerm : AddressTerm 6 :=
  maxAddressTerm (reentrantQueryCapTerm (.reg 0) (.reg 1)) (11*(.reg 0+1)+42)+1

def initialResidentRowTerm : AddressTerm 6 := 128+.reg 4+.reg 5+.reg 2+.reg 3+.reg 0

def initialResidentFloorTerm : AddressTerm 6 := initialResidentRowTerm+.reg 0+1

private def storeTerm (e : AddressTerm 6) (dest : ℕ) : Block :=
  .seq (e.code 6) (.op (.addrCopy dest 6))

def initialResidentHeader : Block :=
  .seq (CursorBind.script bindings) <| .seq (storeTerm initialResidentCapacityTerm 60) <|
  .seq (storeTerm initialResidentRowTerm 67) (storeTerm initialResidentFloorTerm 97)

def initialResidentBlock : Block := .seq initialResidentHeader symbolicWorkspaceBlock

noncomputable def initialResidentTermsCost : Polynomial ℕ :=
  initialResidentCapacityTerm.boundCost+initialResidentRowTerm.boundCost+initialResidentFloorTerm.boundCost+9

noncomputable def initialResidentClock (H d fuel : ℕ) : ℕ :=
  initialResidentTermsCost.eval H + symbolicWorkspaceSteps d fuel

noncomputable def initialResidentBound (H d fuel : ℕ) : ℕ :=
  max H (addressBudget (initialResidentBlock.compile 0))+initialResidentClock H d fuel

private structure Stored (m t : Memory ℚ) (dest value : ℕ) : Prop where
  data : t.data=m.data
  valueAt : t.index dest=value
  low : ∀ i : Fin 6, t.index i=m.index i
  high : ∀ i, 60 ≤ i → i ≠ dest → t.index i=m.index i

private theorem storeTerm_spec (e : AddressTerm 6) (dest H : ℕ) (env : Fin 6 → ℕ)
    (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P) (hd : 60 ≤ dest)
    (he : ∀ i : Fin 6, m.index i=env i) (hH : ∀ i, env i ≤ H)
    (static : (e.code 6).indexWritesBelow 60 = true) :
    ∃ k t, Block.Eval (Memory.AllData P) (storeTerm e dest) m k t ∧
      k ≤ e.boundCost.eval H+1 ∧ Stored m t dest (e.value env) := by
  obtain ⟨k,s,run,hk,data,low,val⟩ := e.correct env 6 m (by decide) he hm
  let t := s.putIndex dest (s.index 6)
  have fin : Block.Eval (Memory.AllData P) (.op (.addrCopy dest 6)) s 1 t :=
    Block.Eval.op_addrCopy _ _ _ run.safe_end run.safe_end
  refine ⟨k+1,t,run.seq fin,Nat.add_le_add_right (hk.trans (e.cost_le env H hH)) 1,
    data,(Memory.putIndex_same ..).trans val,?_,?_⟩
  · intro i
    exact (Memory.putIndex_ne _ (by have := i.isLt;omega) _).trans (low i i.isLt)
  · intro i hi hne
    exact (Memory.putIndex_ne _ hne _).trans (run.index_frame static hi)

structure InitialResidentHeader (m t : Memory ℚ) (L : Buffers) (d fuel : ℕ) : Prop where
  data : t.data=m.data
  capacity : t.index 60=symbolicQueryCap d fuel+1
  row : t.index 67=initialResidentRow L d
  floor : t.index 97=initialResidentRow L d+d+1
  high : ∀ i, 60 ≤ i → i ≠ 60 → i ≠ 67 → i ≠ 97 → t.index i=m.index i

theorem initialResidentHeader_spec {d fuel prec H : ℕ} {L : Buffers} {mag : ℕ → ℚ}
    (m : Memory ℚ) {P : ℚ → Prop} (cache : StableCache m L d fuel prec mag)
    (hm : m.AllData P) (indexBound : ∀ i,m.index i ≤ H) :
    ∃ k t, Block.Eval (Memory.AllData P) initialResidentHeader m k t ∧ k ≤ initialResidentTermsCost.eval H ∧
      InitialResidentHeader m t L d fuel := by
  let u := CursorBind.install bindings m
  let env := inputs m
  have prep := CursorBind.run bindings m hm
  have high (i : ℕ) (hi : 6 ≤ i) : u.index i=m.index i := prep.index_frame (R:=6) (by decide) hi
  have read (i : Fin 6) : u.index i=env i := by
    fin_cases i <;> simp [u,env,inputs,bindings,CursorBind.install,CursorBind.apply]
  have bound (i : Fin 6) : env i ≤ H := by
    fin_cases i <;> apply indexBound
  obtain ⟨k1,s,e1,h1,p1⟩ := storeTerm_spec initialResidentCapacityTerm 60 H env u prep.safe_end
    (by decide) read bound (by decide)
  have sRead (i : Fin 6) : s.index i=env i := (p1.low i).trans (read i)
  obtain ⟨k2,v,e2,h2,p2⟩ := storeTerm_spec initialResidentRowTerm 67 H env s e1.safe_end
    (by decide) sRead bound (by decide)
  have vRead (i : Fin 6) : v.index i=env i := (p2.low i).trans (sRead i)
  obtain ⟨k3,t,e3,h3,p3⟩ := storeTerm_spec initialResidentFloorTerm 97 H env v e2.safe_end
    (by decide) vRead bound (by decide)
  have cap : initialResidentCapacityTerm.value env=symbolicQueryCap d fuel+1 := by
    change (maxAddressTerm (reentrantQueryCapTerm (.reg 0) (.reg 1)) (11*(.reg 0+1)+42)).value env+1=_
    rw [maxAddressTerm_value,reentrantQueryCapTerm_value]
    change max (reentrantQueryCap (m.index 83) (m.index 84)) (11*(m.index 83+1)+42)+1=_
    rw [cache.header.size,cache.header.fuelReg]
    rfl
  have row : initialResidentRowTerm.value env=initialResidentRow L d := by
    change 128+m.index 80+m.index 81+m.index 86+m.index 82+m.index 83=_
    rw [cache.header.magnitudes,cache.header.numerators,cache.header.scalePtr,cache.header.flags,cache.header.size]
    rfl
  have floor : initialResidentFloorTerm.value env=initialResidentRow L d+d+1 := by
    change initialResidentRowTerm.value env+m.index 83+1=_
    rw [row,cache.header.size]
  refine ⟨6+(k1+(k2+k3)),t,prep.seq (e1.seq (e2.seq e3)),?_,p3.data.trans (p2.data.trans p1.data),
    (p3.high 60 (by decide) (by decide)).trans ((p2.high 60 (by decide) (by decide)).trans (p1.valueAt.trans cap)),
    (p3.high 67 (by decide) (by decide)).trans (p2.valueAt.trans row),p3.valueAt.trans floor,?_⟩
  · simp only [initialResidentTermsCost,eval_add,eval_ofNat];omega
  · intro i hi h60 h67 h97
    exact (p3.high i hi h97).trans ((p2.high i hi h67).trans ((p1.high i hi h60).trans (high i (by omega))))

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
