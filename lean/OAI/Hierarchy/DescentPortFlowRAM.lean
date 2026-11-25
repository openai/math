import OAI.Hierarchy.DescentExprScale
import OAI.Hierarchy.DescentPortFlow
import OAI.Hierarchy.DescentCensusRAM

namespace OAI
/-! # Publishing the two-sided old-core flow at every live neighbor slot -/
namespace Hierarchy.DescentPortFlow
open DescentColonies DescentSixParty
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing Classical BigOperators
noncomputable section

variable {w H Δ n k : ℕ}
structure Columns where
  edge : Bank
  slot : Bank
  src : Bank
  dst : Bank
  width : Bank
  core : Bank
  host : Bank
  block : Bank
  neighbor : Bank
  hostOffset : Bank
  blockOffset : Bank

def Columns.all (C : Columns) :=
  [C.edge,C.slot,C.src,C.dst,C.width,C.core,C.host,C.block,C.neighbor,C.hostOffset,C.blockOffset]

def ordinal {E : Type} (old : E≃Fin n) (Δ : ℕ) : (E×Fin Δ) ≃ Fin (n*Δ) :=
  (old.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def siteExpr (C : Columns) (rev : Bool) : Expr :=
  .lookup (if rev then C.dst else C.src) (.lookup C.edge .row)

def positionExpr (C : Columns) (rev : Bool) : Expr := .lookup C.host (siteExpr C rev)

def portExpr (C : Columns) (rev : Bool) : Expr :=
  .op .add (.lookup C.hostOffset (positionExpr C rev)) (.lookup C.slot .row)

def keyExpr (C : Columns) (base : ℕ) (rev : Bool) : Expr :=
  .op .add (.lit base) (.op .add (.lookup C.blockOffset (portExpr C rev)) (.lookup C.block (siteExpr C rev)))

def amountExpr (C : Columns) (wire : ℕ) (rev : Bool) : Expr :=
  .branch .eq (.lookup C.core (.lookup C.edge .row)) (.lit 1)
    (.branch .eq (.lookup C.neighbor (portExpr C rev)) (positionExpr C (!rev))
      (scale (.lookup C.width (.lookup C.edge .row)) wire) (.lit 0)) (.lit 0)

def target (H : ℕ) (dest : Option (Fin H)) := dest.elim H Fin.val

structure Resident (m : Memory w) (b : Bank) (index value : ℕ) : Prop where
  index_lt : index<b.size
  word : m (b.base+index)=(value:Word w)

theorem Resident.read {m : Memory w} {b : Bank} {index value first : ℕ} (h : Resident m b index value)
    (fits : b.Fits w first) : b.read m (index:Word w)=(value:Word w) := by
  simpa [Bank.read,Fin.val_cast_of_lt (h.index_lt.trans fits.2.1),Nat.mod_eq_of_lt h.index_lt] using h.word

variable {F P V : Type} [Field F] [Fintype V] {d : ℕ} {bits : P→ℕ}
  (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
  (name : V≃Fin H) (old : W.graph.Edge≃Fin n) (site : W.graph.Site↪ℕ)
  (next : Fin H×Fin Δ→Option (Fin H))

/-- The five graph columns consist of the chronological old endpoints, mark and
width, plus the old site-to-host/block names. Only edge/slot indices and the
two offset products are immutable arithmetic constants. -/
structure Inputs (C : Columns) (m : Memory w) : Prop where
  edge : ∀ j : W.graph.Edge×Fin Δ,Resident m C.edge (ordinal old Δ j).val (old j.1).val
  slot : ∀ j : W.graph.Edge×Fin Δ,Resident m C.slot (ordinal old Δ j).val j.2.val
  src : ∀ e,Resident m C.src (old e).val (site (W.graph.src e))
  dst : ∀ e,Resident m C.dst (old e).val (site (W.graph.dst e))
  width : ∀ e,Resident m C.width (old e).val (W.graph.width e)
  core : ∀ e,Resident m C.core (old e).val (if e∈W.core then 1 else 0)
  host : ∀ v,Resident m C.host (site v) (name (pos v)).val
  block : ∀ v,Resident m C.block (site v) (ix v).val
  neighbor : ∀ v : Fin H,∀ s : Fin Δ,Resident m C.neighbor (v.val*Δ+s.val) (target H (next (v,s)))
  hostOffset : ∀ v : Fin H,Resident m C.hostOffset v.val (v.val*Δ)
  blockOffset : ∀ v : Fin H,∀ s : Fin Δ,Resident m C.blockOffset (v.val*Δ+s.val) ((v.val*Δ+s.val)*2^k)

variable {C : Columns} {m : Memory w} {first : ℕ}
  (data : Inputs W pos ix name old site next C m) (fits : ∀b∈C.all,b.Fits w first)

include data fits in
omit [Field F] [Fintype V] in
private theorem site_read (rev : Bool) (p : W.graph.Edge×Fin Δ) :
    (siteExpr C rev).eval m ((ordinal old Δ p).val:Word w)=(site (endpoint W rev p.1):Word w) := by
  cases rev <;> simp only [siteExpr,Expr.eval,Bool.false_eq_true,ite_false,ite_true,
    (data.edge p).read (fits _ (by simp [Columns.all])),(data.src p.1).read (fits _ (by simp [Columns.all])),
    (data.dst p.1).read (fits _ (by simp [Columns.all])),endpoint]

include data fits in
omit [Field F] [Fintype V] in
private theorem pos_read (rev : Bool) (p : W.graph.Edge×Fin Δ) :
    (positionExpr C rev).eval m ((ordinal old Δ p).val:Word w)=((name (pos (endpoint W rev p.1))).val:Word w) := by
  rw [positionExpr,Expr.eval,site_read W pos ix name old site next data fits]
  exact (data.host _).read (fits _ (by simp [Columns.all]))

include data fits in
omit [Field F] [Fintype V] in
private theorem port_read (rev : Bool) (p : W.graph.Edge×Fin Δ) :
    (portExpr C rev).eval m ((ordinal old Δ p).val:Word w)=
      ((name (pos (endpoint W rev p.1))).val*Δ+p.2.val : ℕ) := by
  simp only [portExpr,Expr.eval,pos_read W pos ix name old site next data fits,
    (data.hostOffset _).read (fits _ (by simp [Columns.all])),(data.slot p).read (fits _ (by simp [Columns.all])),
    RowOp.opcode,BinaryOp.eval,Nat.cast_add]

include data fits in
omit [Field F] [Fintype V] in
theorem key_read (base : ℕ) (rev : Bool) (p : W.graph.Edge×Fin Δ) :
    (keyExpr C base rev).eval m ((ordinal old Δ p).val:Word w)=
      (base+(portKey W pos ix name rev p).val : ℕ) := by
  have offset := (data.blockOffset (name (pos (endpoint W rev p.1))) p.2).read
    (fits C.blockOffset (by simp [Columns.all]))
  simp only [keyExpr,Expr.eval,port_read W pos ix name old site next data fits,
    site_read W pos ix name old site next data fits,offset,
    (data.block _).read (fits _ (by simp [Columns.all])),RowOp.opcode,BinaryOp.eval,portKey,code_val]
  simp only [Nat.cast_add]

include data fits in
omit [Field F] [Fintype V] in
theorem amount_read (wordPos : 0<w) (room : H<2^w) (wire : ℕ) (rev : Bool) (p : W.graph.Edge×Fin Δ) :
    (amountExpr C wire rev).eval m ((ordinal old Δ p).val:Word w)=(portAmount W pos name next wire rev p:Word w) := by
  have flag : (1:Word w)≠0 := by
    intro eq
    have bad : (((1:ℕ):Word w)).val=0 := congrArg Fin.val eq
    rw [Fin.val_cast_of_lt (Nat.one_lt_pow wordPos.ne' (by decide : 1<2))] at bad
    omega
  let owner:=name (pos (endpoint W rev p.1))
  let peer:=name (pos (endpoint W (!rev) p.1))
  have target_fit : target H (next (owner,p.2))<2^w := by
    cases hit : next (owner,p.2) with
    | none=>exact room
    | some u=>exact u.isLt.trans room
  have same : ((target H (next (owner,p.2)) : ℕ) : Word w)=(peer.val:Word w) ↔ next (owner,p.2)=some peer := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt target_fit,Fin.val_cast_of_lt (peer.isLt.trans room)]
    cases hit : next (owner,p.2) with
    | none => simp [target,Nat.ne_of_gt peer.isLt]
    | some u=>simp [target,Fin.ext_iff]
  simp only [amountExpr,Expr.eval,(data.edge p).read (fits _ (by simp [Columns.all])),
    (data.core p.1).read (fits _ (by simp [Columns.all])),port_read W pos ix name old site next data fits,
    (data.neighbor _ _).read (fits _ (by simp [Columns.all])),pos_read W pos ix name old site next data fits,
    scale_eval,(data.width p.1).read (fits _ (by simp [Columns.all])),DescriptorExpr.Comparison.test,
    beq_iff_eq,portAmount,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Nat.cast_mul]
  by_cases mark : p.1∈W.core <;> simp [mark,flag,Ne.symm flag,owner,peer] at *
  by_cases found : next (name (pos (endpoint W rev p.1)),p.2) =
      some (name (pos (endpoint W (!rev) p.1)))
  · rw [ite_eq_left (same.mpr found),ite_eq_left found]
  · rw [ite_eq_right (fun eq => found (same.mp eq)),ite_eq_right found]

include fits in
private theorem terms_fit (wire base : ℕ) (rev : Bool) :
    (keyExpr C base rev).Fits w first ∧ (amountExpr C wire rev).Fits w first := by
  have scaled := scale_fits (w:=w) (.lookup C.width (.lookup C.edge .row)) wire
    (show (Expr.lookup C.width (.lookup C.edge .row)).Fits w first from
      ⟨fits _ (by simp [Columns.all]),fits _ (by simp [Columns.all]),trivial⟩)
  have hEdge:=fits C.edge (by simp [Columns.all])
  have hSlot:=fits C.slot (by simp [Columns.all])
  have hSrc:=fits C.src (by simp [Columns.all])
  have hDst:=fits C.dst (by simp [Columns.all])
  have hCore:=fits C.core (by simp [Columns.all])
  have hHost:=fits C.host (by simp [Columns.all])
  have hBlock:=fits C.block (by simp [Columns.all])
  have hNeighbor:=fits C.neighbor (by simp [Columns.all])
  have hOffset:=fits C.hostOffset (by simp [Columns.all])
  have hBlockOffset:=fits C.blockOffset (by simp [Columns.all])
  cases rev <;> simp [keyExpr,amountExpr,siteExpr,positionExpr,portExpr,Expr.Fits,
    scaled,hEdge,hSlot,hSrc,hDst,hCore,hHost,hBlock,hNeighbor,hOffset,hBlockOffset]

def nativeKey (rev : Bool) (j : Fin (n*Δ)) :=
  portKey W pos ix name rev ((ordinal old Δ).symm j)
def nativeAmount (wire : ℕ) (rev : Bool) (j : Fin (n*Δ)) :=
  portAmount W pos name next wire rev ((ordinal old Δ).symm j)

omit [Field F] [Fintype V] in
theorem native_sum (wire : ℕ) (rev : Bool) (v : Fin H) (s : Fin Δ) (i : Block k) :
    DescentCensusRAM.sumAt (nativeKey W pos ix name old rev) (nativeAmount W pos name old next wire rev)
      (code H Δ k ((v,s),i))=atPort W pos ix name next wire rev v s i := by
  unfold DescentCensusRAM.sumAt
  rw [←(ordinal old Δ).sum_comp]
  simp [nativeKey,nativeAmount,atPort]

variable (S : DescentCensusRAM.Banks w (n*Δ) ((H*Δ)*2^k))
def program (C : Columns) (wire : ℕ) :=
  (DescentCensusRAM.tally S (keyExpr C S.bins false) (amountExpr C wire false)).seq
    (DescentCensusRAM.add S (keyExpr C S.bins true) (amountExpr C wire true))
def ticks (C : Columns) (wire : ℕ) :=
  DescentCensusRAM.tallyCost S (keyExpr C S.bins false) (amountExpr C wire false)+
    DescentCensusRAM.addCost S (keyExpr C S.bins true) (amountExpr C wire true)

theorem key_work (C : Columns) (base : ℕ) (rev : Bool) : (keyExpr C base rev).work=55 := by cases rev <;> rfl

theorem amount_work (C : Columns) (wire : ℕ) (rev : Bool) : (amountExpr C wire rev).work=70+13*wire := by
  cases rev <;> simp [amountExpr,portExpr,positionExpr,siteExpr,Expr.work,scale_work] <;> omega

/-- The two scans visit original weighted cables, independent of their bit widths.
Clearing the entire sparse port/block bank costs a further six ticks per bin. -/
theorem ticks_eq (C : Columns) (wire : ℕ) : ticks S C wire=
    54+6*((H*Δ)*2^k)+(652+52*wire)*(n*Δ) := by
  simp only [ticks,DescentCensusRAM.tallyCost,DescentCensusRAM.addCost,DescentCensusRAM.issueCost,
    ProtocolRAMGeneratedWrite.work,DescentCensusRAM.slot,Expr.work,key_work,amount_work]
  ring

include data in
omit [Field F] [Fintype V] in
/-- A single initialized bank accumulates both endpoint orientations. Every
padding port reads zero and every live port contains the original symmetric
load. The room inequality for a subsequent natural-valued read is exactly the
word range of this true sum; the CPU itself always performs word arithmetic. -/
theorem run [DecidableEq V] (fit : ∀b∈C.all,b.Fits w S.first) (wordPos : 0<w) (hroom : H<2^w)
    (wire : ℕ) :
    ∃ after : Memory w,(program S C wire).Exec m after (ticks S C wire) ∧
      (∀ v : V,∀ s : Fin Δ,∀ i : Block k,
        after (S.bins+(code H Δ k ((name v,s),i)).val)=
          ((next (name v,s)).elim 0 (fun u=>pairLoad W pos ix wire v (name.symm u) i) : ℕ)) ∧
      ∀ j<S.first,after j=m j := by
  let key:=keyExpr C S.bins
  let val:=amountExpr C wire
  let tag:=nativeKey W pos ix name old (Δ:=Δ)
  let wt:=nativeAmount W pos name old next wire
  have bound (rev : Bool) : (key rev).Fits w S.first ∧ (val rev).Fits w S.first := terms_fit fit wire S.bins rev
  have keys (rev : Bool) (j : Fin (n*Δ)) :
      (key rev).eval m (j.val:Word w)=((S.bins+(tag rev j).val:ℕ):Word w) := by
    simpa [key,tag,nativeKey] using key_read W pos ix name old site next data fit S.bins rev ((ordinal old Δ).symm j)
  have values (rev : Bool) (j : Fin (n*Δ)) : (val rev).eval m (j.val:Word w)=(wt rev j:Word w) := by
    simpa [val,wt,nativeAmount] using amount_read W pos ix name old site next data fit wordPos hroom wire rev
      ((ordinal old Δ).symm j)
  obtain ⟨mid,step,rows,lower⟩:=DescentCensusRAM.tally_exec S (key false) (val false) (tag false) (wt false) m
    (bound false).1 (bound false).2 (keys false) (values false)
  let out:=DescentCensusRAM.afterAdd S (key true) (val true) (tag true) (wt true) mid
  have step2 : (DescentCensusRAM.add S (key true) (val true)).Exec mid out
      (DescentCensusRAM.addCost S (key true) (val true)) := by
    intro labels registers slots machine
    exact DescentCensusRAM.add_exec S (key true) (val true) (tag true) (wt true) mid
      (bound true).1 (bound true).2
      (fun j=>(eval_below (key true) _ m mid (bound true).1 lower).trans (keys true j))
      (fun j=>(eval_below (val true) _ m mid (bound true).2 lower).trans (values true j)) machine
  refine ⟨out,?_,?_,?_⟩
  · intro P R U machine pc reg pub ep prog pubRegs cfg raw entry eqn
    exact Procedure.Exec.then step step2 machine pc reg pub ep prog pubRegs cfg raw entry eqn
  · intro v s i
    let bin := code H Δ k ((name v,s),i)
    have load : DescentCensusRAM.sumAt (tag false) (wt false) bin +
        DescentCensusRAM.sumAt (tag true) (wt true) bin =
        (next (name v,s)).elim 0 (fun u=>pairLoad W pos ix wire v (name.symm u) i) := by
      dsimp only [bin,tag,wt]
      rw [native_sum W pos ix name old next wire false (name v) s i,
        native_sum W pos ix name old next wire true (name v) s i]
      cases live : next (name v,s) with
      | none =>
        rw [missing W pos ix name next wire false (name v) s i live,
          missing W pos ix name next wire true (name v) s i live]
        simp only [Nat.zero_add, Option.elim]
      | some u =>
        have present : next (name v,s)=some (name (name.symm u)) := by simpa only [Equiv.apply_symm_apply] using live
        exact symmetric_at W pos ix name next wire v (name.symm u) s i present
    calc
      out (S.bins+bin.val) = mid (S.bins+bin.val)+(DescentCensusRAM.sumAt (tag true) (wt true) bin : Word w) :=
        DescentCensusRAM.add_read S (key true) (val true) (tag true) (wt true) mid bin
      _ = ((DescentCensusRAM.sumAt (tag false) (wt false) bin +
          DescentCensusRAM.sumAt (tag true) (wt true) bin : ℕ) : Word w) := by rw [rows bin,Nat.cast_add]
      _ = _ := congrArg (fun amount : ℕ => (amount : Word w)) load
  · intro j hj
    exact (DescentCensusRAM.add_frame S (key true) (val true) (tag true) (wt true) mid j hj).trans (lower j hj)



end
end Hierarchy.DescentPortFlow

end OAI
