import OAI.Hierarchy.DescentPhysicalOrder
import OAI.Hierarchy.DescentEdgeTapePrefix
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Physical site IDs from a sparse occupancy directory and an exclusive prefix -/

namespace Hierarchy.DescentSiteTape
open DescentPhysicalOrder ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {U : Type} [Fintype U] {n w slots R B : ℕ}

/-- The block is the minor coordinate in each public group/host row. -/
def ofCoordinates (pos : U→Fin R) (block : U→Fin B) (inj : Function.Injective (fun u=>(pos u,block u))) : U↪Fin (R*B) :=
  (⟨fun u=>(pos u,block u),inj⟩ : U↪Fin R×Fin B).trans finProdFinEquiv.toEmbedding

omit [Fintype U] in
@[simp] theorem coordinate_word (pos : U→Fin R) (block : U→Fin B)
    (inj : Function.Injective (fun u=>(pos u,block u))) (u : U) :
    (ofCoordinates pos block inj u).val=(pos u).val*B+(block u).val := by
  change (block u).val+B*(pos u).val=_
  ring

def rank (slot : U↪Fin slots) := slot.trans Fin.valEmbedding

def order (slot : U↪Fin slots) := physical (rank slot)

theorem order_val (slot : U↪Fin slots) (u : U) :
    (order slot u).val=(Finset.univ.filter fun v=>(slot v).val<(slot u).val).card := physical_val (rank slot) u

def addresses (base slots : ℕ) := base+slots

def words (base slots n : ℕ) := addresses base slots+n

def starts (base slots n : ℕ) := words base slots n+n

def endAt (base slots n : ℕ) := starts base slots n+slots+1

def destExpr (base : ℕ) (field : Expr) : Expr := .op .add (.lit base) field

private def init (base slots : ℕ) (m : Memory w) := ProtocolRAM.image base slots (.lit 0) m

def clearedScatter (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w) : Memory w :=
  ProtocolRAMGeneratedWrite.image (addresses base slots) (words base slots n) (destExpr base field) (.lit 1)
    (fun i=>base+(index i).val) (fun _=>1) (init base slots m)

def program (w base slots n : ℕ) (field : Expr) :=
  ((scan w base slots (.lit 0)).seq (ProtocolRAMGeneratedWrite.program w (addresses base slots) (words base slots n) n
    (destExpr base field) (.lit 1))).seq (ProtocolRAMEndpointPrefix.exclusive w base (starts base slots n) slots)

def ticks (slots n : ℕ) (field : Expr) := (4+slots*6)+ProtocolRAMGeneratedWrite.work n (destExpr 0 field) (.lit 1)+(10+(3+12*slots))

def after (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w) :=
  ProtocolRAMEndpointPrefix.image (starts base slots n) (DescentEdgeTapePrefix.before (fun _=>1) (rank index))
    (clearedScatter base slots field index m) slots

private theorem scatter_counts (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w)
    (j : Fin slots) : clearedScatter base slots field index m (base+j.val)=
      (DescentEdgeTapePrefix.row (fun _=>1) (rank index) j.val:Word w) := by
  let addr := fun i : Fin n=>base+(index i).val
  have inject : Function.Injective addr := by
    intro i l same
    exact index.injective (Fin.ext (Nat.add_left_cancel same))
  by_cases hit : ∃i,index i=j
  · obtain ⟨i,rfl⟩ := hit
    rw [show DescentEdgeTapePrefix.row (fun _=>1) (rank index) (index i).val=1 from
      DescentEdgeTapePrefix.row_present _ _ (rank index).injective i]
    exact ProtocolRAMIndexedWrite.read_unique addr _ _ inject n le_rfl i i.isLt
  · have missing (i : Fin n) : (rank index) i≠j.val := fun h=>hit ⟨i,Fin.ext h⟩
    rw [DescentEdgeTapePrefix.row_absent _ _ _ missing]
    change ProtocolRAMIndexedWrite.image addr _ _ n (base+j.val)=_
    have away (i : Fin n) : base+j.val≠addr i := fun same=>missing i (Nat.add_left_cancel same.symm)
    rw [ProtocolRAMIndexedWrite.frame addr (fun _=>1) _ n (base+j.val) away]
    have below : base+j.val<addresses base slots := Nat.add_lt_add_left j.isLt _
    have early : base+j.val<words base slots n := below.trans_le (Nat.le_add_right (addresses base slots) n)
    rw [ProtocolRAMGeneratedWrite.frame_image (words base slots n) n (.lit 1) _ _ (Or.inl early),
      ProtocolRAMGeneratedWrite.frame_image (addresses base slots) n (destExpr base field) _ _ (Or.inl below)]
    exact ProtocolRAMGeneratedWrite.read_image base slots (.lit 0) m j

/-- Source rows evaluate the actual stored sparse site address. The machine
clears its finite directory, scatters one per occupied row, and prefixes it. -/
theorem run (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w)
    (fit : field.Fits w base) (room : endAt base slots n<2^w)
    (source : ∀i : Fin n,field.eval m (i.val:Word w)=((index i).val:Word w)) :
    (program w base slots n field).Exec m (after base slots field index m) (ticks slots n field) := by
  have ready : base+slots<2^w := by unfold endAt starts words addresses at room; omega
  let m₀ := init base slots m
  have frame (a : ℕ) (lo : a<base) : m₀ a=m a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl lo)
  have input (i : Fin n) : (destExpr base field).eval m₀ (i.val:Word w)=((base+(index i).val:ℕ):Word w) := by
    simp only [destExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_add,eval_below field _ m m₀ fit frame,source]
  have first : (scan w base slots (.lit 0)).Exec m m₀ (4+slots*6) :=
    scan_exec base slots (.lit 0) m trivial ready
  have middle : (ProtocolRAMGeneratedWrite.program w (addresses base slots) (words base slots n) n
      (destExpr base field) (.lit 1)).Exec m₀ (clearedScatter base slots field index m)
      (ProtocolRAMGeneratedWrite.work n (destExpr base field) (.lit 1)) := ProtocolRAMGeneratedWrite.run (addresses base slots) (words base slots n) (destExpr base field) (.lit 1)
    (fun i : Fin n=>base+(index i).val) (fun _=>1) m₀
    ⟨trivial,ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) fit⟩ trivial le_rfl
    (by unfold endAt starts words addresses at *;omega) input (fun _=>rfl)
    (fun i=>(Nat.add_lt_add_left (index i).isLt _).trans ready)
    (fun i j eqn=>by have := (index j).isLt;unfold addresses at eqn;omega)
    (fun i j eqn=>by have := (index j).isLt;unfold words addresses at eqn;omega)
  have last : (ProtocolRAMEndpointPrefix.exclusive w base (starts base slots n) slots).Exec
      (clearedScatter base slots field index m) (after base slots field index m) (10+(3+12*slots)) :=
    DescentEdgeTapePrefix.physical (fun _ : Fin n=>1) (rank index) (clearedScatter base slots field index m)
    (counts:=base) (starts:=starts base slots n) (n:=slots)
    (by unfold starts words addresses;omega) room (fun j hj=>scatter_counts base slots field index m ⟨j,hj⟩)
  intro P R K machine
  exact Procedure.Exec.then (Procedure.Exec.then first middle) last machine

theorem read (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w) (i : Fin n) :
    after base slots field index m (starts base slots n+(index i).val)=((order index i).val:Word w) := by
  rw [order_val]
  apply (DescentEdgeTapePrefix.physical_read (fun _ : Fin n=>1) (rank index) _ i (index i).isLt.le).trans
  simp [ProtocolRAMPortRanks.«prefix»,rank]

/-- The final exclusive-prefix cell holds the physical number of active sites. -/
theorem total_read (base slots : ℕ) (field : Expr) (index : Fin n↪Fin slots) (m : Memory w) :
    after base slots field index m (starts base slots n+slots)=(n:Word w) := by
  unfold after
  rw [ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl,
    DescentEdgeTapePrefix.before_end (fun _ : Fin n=>1) (rank index) slots (fun i => (index i).isLt)]
  simp

/-- A densely streamed inventory may use any preexisting row enumeration;
the new ID counts earlier physical coordinates on exactly the abstract sites. -/
theorem order_enumerate (enumerate : Fin n≃U) (slot : U↪Fin slots) (i : Fin n) :
    (order (enumerate.toEmbedding.trans slot) i).val=(order slot (enumerate i)).val := by
  rw [order_val,order_val]
  apply Finset.card_bij (fun j _=>enumerate j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  · exact fun _ _ _ _ h=>enumerate.injective h
  · intro v hv
    obtain ⟨j,rfl⟩ := enumerate.surjective v
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩

theorem directory_read (base : ℕ) (field : Expr) (enumerate : Fin n≃U) (slot : U↪Fin slots)
    (m : Memory w) (u : U) : after base slots field (enumerate.toEmbedding.trans slot) m
        (starts base slots n+(slot u).val)=((order slot u).val:Word w) := by
  obtain ⟨i,rfl⟩ := enumerate.surjective u
  exact (read base slots field (enumerate.toEmbedding.trans slot) m i).trans
    (congrArg (fun j : ℕ=>(j:Word w)) (order_enumerate enumerate slot i))

end
end Hierarchy.DescentSiteTape

end OAI
