import OAI.Hierarchy.DescentMarkedCensus
import OAI.Hierarchy.DescentCensusScale

namespace OAI
/-! # Genuine old cable and site fields used by each census pass -/

namespace Hierarchy.DescentSixParty.MarkedCensus
open StarKeys DescentColonies ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section

/-- Edge columns give incident site IDs and marked widths. Site columns
give the original position, block, hub mark and stored atom count. -/
structure Fields where
  source : Bank
  target : Bank
  width : Bank
  core : Bank
  position : Bank
  block : Bank
  hub : Bank
  history : Bank

def Fields.Fits (f : Fields) (w a : ℕ) := f.source.Fits w a ∧ f.target.Fits w a ∧ f.width.Fits w a ∧
    f.core.Fits w a ∧ f.position.Fits w a ∧ f.block.Fits w a ∧ f.hub.Fits w a ∧ f.history.Fits w a

def siteKey (f : Fields) (w k bins : ℕ) (id : Expr) : Expr :=
  .op .add (.lit bins) (.op .add (.lookup f.block id) (scale (2^k) (.lookup f.position id) w))

def endKey (f : Fields) (w k bins : ℕ) (side : Bool) : Expr :=
  siteKey f w k bins (.lookup (if side then f.target else f.source) .row)

def endUnits (f : Fields) (w wire β : ℕ) (side : Bool) : Expr :=
  .branch .eq (.lookup f.hub (.lookup (if side then f.target else f.source) .row)) (.lit 0)
    (scale wire (.lookup f.width .row) w) (scale (wire*β) (.lookup f.width .row) w)

def histUnits (f : Fields) (w hist : ℕ) : Expr := scale hist (.lookup f.history .row) w

variable {F P V A : Type} [Field F] [Fintype V] [DecidableEq V] {d k n t H w : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (block : W.graph.Site→Block k) (idx : V ≃ Fin H)
variable (edges : Fin n ≃ W.graph.Edge) (sites : Fin t ≃ W.graph.Site)
variable (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List A)

structure SourceRows (f : Fields) (mem : Memory w) : Prop where
  source : ∀i : Fin n,f.source.read mem (i.val:Word w)=((sites.symm (W.graph.src (edges i))).val:Word w)
  target : ∀i : Fin n,f.target.read mem (i.val:Word w)=((sites.symm (W.graph.dst (edges i))).val:Word w)
  width : ∀i : Fin n,f.width.read mem (i.val:Word w)=(W.graph.width (edges i):Word w)
  core : ∀i : Fin n,f.core.read mem (i.val:Word w)=(marked W (edges i):Word w)
  position : ∀i : Fin t,f.position.read mem (i.val:Word w)=((idx (pos (sites i))).val:Word w)
  place : ∀i : Fin t,f.block.read mem (i.val:Word w)=((block (sites i)).val:Word w)
  mark : ∀i : Fin t,f.hub.read mem (i.val:Word w)=((if hub (sites i) then 1 else 0:ℕ):Word w)
  saved : ∀i : Fin t,f.history.read mem (i.val:Word w)=((atoms (sites i)).length:Word w)

omit [Field F] [Fintype V] [DecidableEq V] in
theorem site_key_read {f : Fields} {mem : Memory w} (h : SourceRows W pos block idx edges sites hub atoms f mem)
    (bins : ℕ) (i : Fin t) (x : Expr) (r : Word w) (hx : x.eval mem r=(i.val:Word w)) :
    (siteKey f w k bins x).eval mem r=((bins+(address W pos block idx (sites i)).val:ℕ):Word w) := by
  simp only [siteKey,Expr.eval,RowOp.opcode,BinaryOp.eval,full_scale,hx,h.position,h.place,
    address,finProdFinEquiv_apply_val,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

omit [Field F] [Fintype V] [DecidableEq V] in
theorem key_read {f : Fields} {mem : Memory w} (h : SourceRows W pos block idx edges sites hub atoms f mem)
    (bins : ℕ) (side : Bool) (i : Fin n) :
    (endKey f w k bins side).eval mem (i.val:Word w)=
      ((bins+(address W pos block idx ((if side then W.graph.dst else W.graph.src) (edges i))).val:ℕ):Word w) := by
  cases side
  · simpa only [endKey,Bool.false_eq_true,ite_false,Equiv.apply_symm_apply] using
      site_key_read W pos block idx edges sites hub atoms h bins (sites.symm (W.graph.src (edges i)))
        (.lookup f.source .row) (i.val:Word w) (h.source i)
  · simpa only [endKey,ite_true,Equiv.apply_symm_apply] using
      site_key_read W pos block idx edges sites hub atoms h bins (sites.symm (W.graph.dst (edges i)))
        (.lookup f.target .row) (i.val:Word w) (h.target i)

omit [Field F] [Fintype V] [DecidableEq V] in
theorem units_read {f : Fields} {mem : Memory w} (h : SourceRows W pos block idx edges sites hub atoms f mem)
    (wide : 1<2^w) (wire β : ℕ) (side : Bool) (i : Fin n) :
    (endUnits f w wire β side).eval mem (i.val:Word w)=
      (terminalWeight W hub wire β (if side then W.graph.dst else W.graph.src) (edges i):Word w) := by
  have ne : (1:Word w)≠0 := by
    intro eqn
    have hx := congrArg Fin.val eqn
    change (((1:ℕ):Word w).val)=0 at hx
    rw [Fin.val_cast_of_lt wide] at hx
    contradiction
  cases side <;> simp only [endUnits,terminalWeight,Bool.false_eq_true,ite_false,ite_true,Expr.eval,full_scale,
    h.source,h.target,h.mark,h.width,Equiv.apply_symm_apply,Comparison.test] <;>
    split <;> simp_all [Nat.cast_mul,mul_comm,mul_assoc,mul_left_comm]

omit [Field F] [Fintype V] [DecidableEq V] in
theorem hist_read {f : Fields} {mem : Memory w} (h : SourceRows W pos block idx edges sites hub atoms f mem)
    (hist : ℕ) (i : Fin t) : (histUnits f w hist).eval mem (i.val:Word w)=(historyWeight W atoms hist (sites i):Word w) := by
  simp [histUnits,full_scale,h.saved,Expr.eval,historyWeight]

end
end Hierarchy.DescentSixParty.MarkedCensus

end OAI
