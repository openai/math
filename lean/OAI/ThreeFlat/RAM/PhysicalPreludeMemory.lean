import OAI.ThreeFlat.RAM.PhysicalImageData
import OAI.ThreeFlat.RAM.PhysicalInputCopy

namespace OAI
/-! # Memory contents between the six phases of the physical H initializer -/

namespace ThreeFlat.RAM.PhysicalPrelude.Image

open Computability.VPVNP.BurstRAM BitLayout
open scoped Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {w : ℕ} (I : Image F w)

noncomputable def staged (m : Memory w) : Memory w :=
  PhysicalInputCopy.copied 0 I.sizes.rawCount I.sizes.scratch m

noncomputable def packMem (m : Memory w) : Memory w :=
  FixedTraceImage.packed I.G I.field I.keys I.sizes.gateBase (I.staged m)

noncomputable def paramMem (m : Memory w) : Memory w :=
  PhysicalInputCopy.copied (I.sizes.scratch+I.sizes.rawParams) I.parameters
    I.sizes.parameterBase (I.packMem m)

noncomputable def traceMem (m : Memory w) : Memory w :=
  fillSegment I.sizes.templateBase (11*I.X.cells)
    (PhysicalTraceSource.rowWord I.X I.field I.sizes.templateBase) (I.paramMem m)

noncomputable def lowMem (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (m : Memory w) : Memory w :=
  fillSegment 0 I.firstCell (memory I.H I.field (PhysicalPinsInput.logical D x y) (fun _=>false))
    (I.traceMem m)

noncomputable def finalMem (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (m : Memory w) : Memory w :=
  fillSegment I.firstProduct (products (F:=F))
    (memory I.H I.field (PhysicalPinsInput.logical D x y) (fun _=>false)) (I.lowMem D x y m)

private theorem stagedAt (m : Memory w) (j : ℕ) (h : j < I.sizes.rawCount) :
    I.staged m (I.sizes.scratch+j) = m j := by
  simpa only [staged,Nat.zero_add] using
    PhysicalInputCopy.copied_at 0 I.sizes.rawCount I.sizes.scratch m j h

private theorem packedBeforeScratch :
    I.sizes.gateBase+FixedTraceImage.count I.G ≤ I.sizes.scratch :=
  I.sizes.packedEnd_eq.symm.trans_le I.sizes.scratch_after_packed

private theorem templateBeforeScratch : I.sizes.templateBase+11*I.X.cells ≤ I.sizes.scratch :=
  (Nat.le_add_right I.sizes.gateBase _).trans (I.packedBeforeScratch)

private theorem paramsBeforeGate : I.sizes.parameterBase+I.parameters ≤ I.sizes.gateBase :=
  Nat.le_add_right I.sizes.templateBase _

private theorem packScratch (m : Memory w) (j : ℕ) :
    I.packMem m (I.sizes.scratch+j) = I.staged m (I.sizes.scratch+j) := by
  have h := I.packedBeforeScratch
  have e : ¬ I.sizes.scratch+j < I.sizes.gateBase+FixedTraceImage.count I.G := by omega
  simp [packMem,FixedTraceImage.packed,fillSegment,e]

private theorem paramAfter (m : Memory w) (a : ℕ) (h : I.sizes.parameterBase+I.parameters ≤ a) :
    I.paramMem m a = I.packMem m a :=
  PhysicalInputCopy.copied_outside _ _ _ _ _ (Or.inr h)

private theorem traceOutside (m : Memory w) (a : ℕ)
    (h : a < I.sizes.templateBase ∨ I.sizes.templateBase+11*I.X.cells ≤ a) :
    I.traceMem m a = I.paramMem m a := by
  have h' : ¬ (I.sizes.templateBase ≤ a ∧ a < I.sizes.templateBase+11*I.X.cells) := by omega
  exact ite_eq_right h'

private theorem firstCell_le_firstProduct : I.firstCell ≤ I.firstProduct :=
  Nat.le_add_right _ _

variable {I}
variable {D : Fin I.advice → Bool} {x y : Fin I.endpointBits → Bool}
variable {params : Fin I.parameters → Bool} {m : Memory w}
variable (I)

/-- Staging retains every source bit used to pack the local gates and port formulas. -/
theorem packInput (h : I.Raw D x y params m) (j : Fin (w*FixedTraceImage.count I.G)) :
    I.staged m (I.sizes.scratch+I.sizes.rawTable+j.val) =
      ((FixedTraceImage.parameter I.G I.field I.keys j).toNat : Word w) := by
  rw [Nat.add_assoc,I.stagedAt m _ (Nat.add_lt_add_left j.isLt I.sizes.rawTable)]
  exact h.metadata j

theorem traceGate (m : Memory w) (i : Fin I.G.cells) (j : Fin 11) :
    I.paramMem m (I.sizes.gateBase+11*i.val+j.val) = record I.G I.field i j := by
  have h := I.paramsBeforeGate
  rw [I.paramAfter m _ (by omega)]
  exact FixedTraceImage.packed_gate _ _ _ _ _ _ _

theorem tracePort (m : Memory w) (i : Fin I.ports) (j : Fin 11) :
    I.paramMem m (TraceAddressReader.address I.sizes.portBase i.val j) =
      (TraceAddressReader.fields (I.keys i) j : Word w) := by
  have h := I.paramsBeforeGate
  have p : I.sizes.portBase = I.sizes.gateBase+11*I.G.cells := rfl
  rw [I.paramAfter m _ (by unfold TraceAddressReader.address; omega)]
  exact FixedTraceImage.packed_port _ _ _ _ _ _ _

/-- The parameter and gate arrays are disjoint from the whole staged prefix. -/
theorem paramMem_staged (m : Memory w) (j : ℕ) (hj : j<I.sizes.rawCount) :
    I.paramMem m (I.sizes.scratch+j) = m j := by
  have packed := I.packedBeforeScratch
  have paramsLow := I.paramsBeforeGate
  rw [I.paramAfter m _ (by omega),I.packScratch,I.stagedAt m j hj]

/-- The original endpoint pairs and advice still occupy their staged positions
after materialization of the trace template. -/
theorem lowInput (h : I.Raw D x y params m) (j : ℕ) (hj : j < I.sizes.rawParams) :
    I.traceMem m (I.sizes.scratch+j) = bitWord w (PhysicalPinsInput.rawBit D x y j) := by
  have gate : I.sizes.templateBase+11*I.X.cells = I.sizes.gateBase := rfl
  have high := I.templateBeforeScratch
  have paramsLow := I.paramsBeforeGate
  have hc : I.sizes.rawTable ≤ I.sizes.rawCount := Nat.le_add_right _ _
  have hp : I.sizes.rawParams ≤ I.sizes.rawTable := Nat.le_add_right _ _
  rw [I.traceOutside m _ (Or.inr (by omega)),I.paramAfter m _ (by omega),
    I.packScratch,I.stagedAt m _ (by omega)]
  exact h.input j hj

private theorem readParam (h : I.Raw D x y params m) (j : Fin I.parameters) :
    I.paramMem m (I.sizes.parameterBase+j.val) = bitWord w (params j) := by
  have t : I.sizes.rawParams+I.parameters = I.sizes.rawTable := rfl
  have hc : I.sizes.rawTable ≤ I.sizes.rawCount := Nat.le_add_right _ _
  have jlt := j.isLt
  rw [paramMem,PhysicalInputCopy.copied_at _ _ _ _ _ j.isLt,Nat.add_assoc,I.packScratch,
    I.stagedAt m _ (by omega)]
  exact h.parameters j

private theorem finalHigh (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (m : Memory w) (a : ℕ) (h : footprint I.H ≤ a) :
    I.finalMem D x y m a = I.traceMem m a := by
  have hp : I.firstProduct+products (F:=F) ≤ a := h
  have hc := I.firstCell_le_firstProduct
  simp [finalMem,lowMem,fillSegment,Nat.not_lt_of_ge hp,show ¬ a < I.firstCell by omega]

/-- At H entry the low pins, product coefficients, independent parameter bits,
and all eleven columns of the expanded trace records coexist in memory. -/
theorem finalReady (h : I.Raw D x y params m) : I.Ready D x y params (I.finalMem D x y m) := by
  constructor
  · intro a ha
    have hc := I.firstCell_le_firstProduct
    simp [finalMem,lowMem,fillSegment,show ¬ I.firstProduct ≤ a by omega,ha]
  · intro a ha hb
    have endAt : a < I.firstProduct+products (F:=F) := hb
    simp [finalMem,fillSegment,ha,endAt]
  · intro j
    have start : footprint I.H = I.sizes.parameterBase := rfl
    have stop : I.sizes.parameterBase+I.parameters = I.sizes.templateBase := rfl
    have jlt := j.isLt
    rw [I.finalHigh _ _ _ _ _ (by omega),I.traceOutside m _ (Or.inl (by omega))]
    exact I.readParam h j
  · intro i j
    have start : footprint I.H ≤ I.sizes.templateBase := Nat.le_add_right I.sizes.parameterBase _
    rw [I.finalHigh _ _ _ _ _ (by omega)]
    exact PhysicalTraceSource.generated_at I.G I.field I.input I.sizes.templateBase (I.paramMem m) i j

end ThreeFlat.RAM.PhysicalPrelude.Image

end OAI
