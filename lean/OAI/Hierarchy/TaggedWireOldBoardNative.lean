import OAI.Hierarchy.TaggedWireTurnBoardNative
import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # Native direction and width of the old item in the true turn chart -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open WireTelescope ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Hierarchy.ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

structure Inventory where
  kind : Expr
  index : Expr
  paid : Bank
  active : Bank
  reserved : Bank
  used : Bank

def Inventory.width (g : Inventory) : Expr :=
  .branch .eq g.kind (.lit 0) (.lookup g.paid g.index)
    (.branch .eq g.kind (.lit 1) (.lookup g.active g.index)
      (.op .sub (.lookup g.reserved g.index) (.lookup g.used g.index)))

theorem Inventory.width_paid {w : ℕ} (g : Inventory) (m : Memory w) (r j : Word w)
    (tag : g.kind.eval m r=0) (idx : g.index.eval m r=j) : g.width.eval m r=g.paid.read m j := by
  simp [width,Expr.eval,tag,idx,Comparison.test]

theorem Inventory.width_goods {w : ℕ} (g : Inventory) (m : Memory w) (r j : Word w)
    (one : (1:Word w)≠0) (tag : g.kind.eval m r=1) (idx : g.index.eval m r=j) :
    g.width.eval m r=g.active.read m j := by simp [width,Expr.eval,tag,idx,Comparison.test,one]

theorem Inventory.width_catalyst {w : ℕ} (g : Inventory) (m : Memory w) (r j : Word w)
    (tag₀ : g.kind.eval m r≠0) (tag₁ : g.kind.eval m r≠1) (idx : g.index.eval m r=j)
    (fund : (g.used.read m j).val≤(g.reserved.read m j).val) :
    (g.width.eval m r).val=(g.reserved.read m j).val-(g.used.read m j).val := by
  simp only [width,Expr.eval,Comparison.test,beq_iff_eq,Nat.cast_zero,Nat.cast_one,
    ite_eq_right tag₀,ite_eq_right tag₁,idx,RowOp.opcode,BinaryOp.eval]
  exact Fin.sub_val_of_le fund

/-- The ROM sits above the real chart inputs and below all generated work.
Its rows are the exact old source enumeration of matrixLayout. -/
def Inventory.decode {edges : ℕ} {I A : Type} [Fintype I] [Fintype A]
    (ci : I→ℕ) (cj : A→ℕ) (kind : Bool) (r : Fin (Fintype.card (SettledMatrix.Source edges I A))) : ℕ :=
  match SettledMatrix.Layout.numbered (r:=edges) (I:=I) (A:=A) r with
  | .inl p=>if kind then 0 else p.val
  | .inr (.inl i)=>if kind then 1 else ci i
  | .inr (.inr a)=>if kind then 2 else cj a

def Inventory.ofOriginal (base n : ℕ) (paid active reserved used : Bank) : Inventory :=
  ⟨RoleROM.expr base n .row,RoleROM.expr (base+n) n .row,paid,active,reserved,used⟩

theorem Inventory.original_read {w edges : ℕ} {I A : Type} [Fintype I] [Fintype A]
    (ci : I→ℕ) (cj : A→ℕ) (m : Memory w) (base : ℕ) (paid active reserved used : Bank)
    (n : ℕ) (size : n=Fintype.card (SettledMatrix.Source edges I A))
    (tags : RoleROM.Mounted base (Inventory.decode (edges:=edges) ci cj true) m)
    (keys : RoleROM.Mounted (base+n) (Inventory.decode (edges:=edges) ci cj false) m)
    (fit : n≤2^w) (r : Fin (Fintype.card (SettledMatrix.Source edges I A))) :
    let chart:=Inventory.ofOriginal base n paid active reserved used
    chart.kind.eval m (r.val:Word w)=((Inventory.decode ci cj true r):Word w) ∧
    chart.index.eval m (r.val:Word w)=((Inventory.decode ci cj false r):Word w) := by
  subst n
  exact ⟨RoleROM.read tags .row _ r fit rfl,RoleROM.read keys .row _ r fit rfl⟩

namespace Board
variable (b : Board) (g : Inventory) {w : ℕ}

def rawFields : Fin 3→Expr := ![socketSite b.chart (b.before false),socketSite b.chart (b.before true),g.width]
def rawPasses := columns b.old b.endAt (List.ofFn (b.rawFields g))
def extended (w : ℕ) := (b.code w).seq (program w (b.rawPasses g))
def extendedTime := b.time+clock (b.rawPasses g)
def extendedState (m : Memory w) := result (b.rawPasses g) (b.final m)

def forwardSite (right : Bool) := RoleROM.bank (b.endAt+right.toNat*b.old) b.old
def widthBank := RoleROM.bank (b.endAt+2*b.old) b.old

theorem extended_exec (m : Memory w) (ready : b.Ready w) (fit : ∀j,(b.rawFields g j).Fits w b.base)
    (room : b.endAt+3*b.old<2^w) :
    (b.extended g w).Exec m (b.extendedState g m) (b.extendedTime g) ∧
    (∀(j : Fin 3) (i : Fin b.old),b.extendedState g m (b.endAt+j.val*b.old+i.val)=
      (b.rawFields g j).eval m (i.val:Word w)) ∧ (∀a,a<b.endAt→b.extendedState g m a=b.final m a) := by
  let es:=List.ofFn (b.rawFields g)
  have lo : b.base≤b.endAt :=
    (Nat.le_add_right b.base (4*b.old)).trans (Nat.le_add_right _ (4*b.edges))
  have safe (e : Expr) (he : e∈es) : e.Fits w b.endAt := by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact ProtocolRAMGeneratedWrite.fits_mono _ lo (fit j)
  have before:=b.output m ready
  refine ⟨Procedure.Exec.then before.1 (columns_exec es (b.final m) (columns_safe es le_rfl safe (by simpa only [es,List.length_ofFn] using room))),?_,?_⟩
  · intro j i
    have val:=columns_read es (b.final m) le_rfl safe j.val (by simpa only [es,List.length_ofFn] using j.isLt) i
    have idx : j.val<es.length := by simpa only [es,List.length_ofFn] using j.isLt
    have sel : es[j.val]=b.rawFields g j := List.getElem_ofFn (f:=b.rawFields g) idx
    exact (val.trans (congrArg (fun e : Expr=>e.eval (b.final m) (i.val:Word w)) sel)).trans
      (ProtocolRAM.eval_below (b.rawFields g j) _ m (b.final m) (fit j) (fun a low=>before.2.2.2 a (.inl low)))
  · intro a low;exact columns_frame es (b.final m) (.inl low)

theorem extended_cheap : CheapCode (b.extended g w) := cheap_seq b.cheapCode (program_cheap w (b.rawPasses g))

end Board
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
