import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Native publication of the selected cell and touch of every simulated rail

The first scan reads the assigned destination of the negative endpoint.
The second reads that cell and extracts its digit in the rail's direction.
Only these two output banks are written.
-/

namespace Hierarchy.GridSimRailScan
open ThreeFlat.RAM PhysicalPinsExpr PhysicalProcedure DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

structure Banks where
  dest : ℕ
  dir : ℕ
  cell : ℕ
  power : ℕ
  touch : ℕ

private abbrev X := Formula 1
private abbrev loadAt (b : ℕ) (i : X) : X := .load (.op .add (.lit b) i)
private abbrev ordinalAt (b : ℕ) : X := .cut (.reg 0) (.lit b)

def cellExpr (B : Banks) (p : ℕ) : X :=
  .op .div (loadAt B.dest (.op .mul (.lit 2) (ordinalAt B.cell))) (.lit p)

def touchExpr (B : Banks) (g : ℕ) : X :=
  let i := ordinalAt B.touch
  .op .mod (.op .div (loadAt B.cell i) (loadAt B.power (loadAt B.dir i))) (.lit g)

@[simp] theorem cellExpr_work (B : Banks) (p : ℕ) : (cellExpr B p).work = 12 := rfl
@[simp] theorem touchExpr_work (B : Banks) (g : ℕ) : (touchExpr B g).work = 22 := rfl

def build (W : ℕ) (B : Banks) (rails g p : ℕ) : Procedure W :=
  (PhysicalInputPhases.writing (HeaderScan.closed (cellExpr B p)) Fin.elim0 B.cell rails).seq
    (PhysicalInputPhases.writing (HeaderScan.closed (touchExpr B g)) Fin.elim0 B.touch rails)

def cost (rails : ℕ) := 8+76*rails

theorem text_size (W : ℕ) (B : Banks) (rails g p : ℕ) :
    let M := build W B rails g p
    M.labels+M.registers+M.slots = 158 := by
  simp [build,Procedure.seq,PhysicalInputPhases.writing,DescriptorExpr.Term.labels_eq,
    HeaderScan.binds_closed]

/-- Both endpoints of a rail are assigned to the same tick. The destination
of the negative endpoint determines the index of its receiving cell. -/
def cellWord {W : ℕ} (B : Banks) (p : ℕ) (m : Memory W) (i : ℕ) : ℕ :=
  (m (B.dest+2*i)).val / p

def touchWord {W : ℕ} (B : Banks) (g p : ℕ) (m : Memory W) (i : ℕ) : ℕ :=
  cellWord B p m i / (m (B.power+(m (B.dir+i)).val)).val % g

private def cellImage {W : ℕ} (B : Banks) (rails p : ℕ) (m : Memory W) : Memory W :=
  fillSegment B.cell rails (fun a => (cellWord B p m (a-B.cell) : Word W)) m

def image {W : ℕ} (B : Banks) (rails g p : ℕ) (m : Memory W) : Memory W :=
  fillSegment B.touch rails (fun a => (touchWord B g p m (a-B.touch) : Word W))
    (cellImage B rails p m)

/-- Ordered page bounds suffice for the two scans. Both division and
remainder follow the native word machine's natural-number conventions. -/
structure Fits (W : ℕ) (B : Banks) (rails axes g p : ℕ) : Prop where
  dirCell : B.dir+rails ≤ B.cell
  cellPower : B.cell+rails ≤ B.power
  powerTouch : B.power+axes ≤ B.touch
  touchDest : B.touch+rails ≤ B.dest
  stop : B.dest+2*rails < 2^W
  radix : g < 2^W
  pins : p < 2^W

theorem cell_at {W : ℕ} (B : Banks) (rails g p : ℕ) (m : Memory W)
    (sep : B.cell+rails ≤ B.touch) (i : ℕ) (hi : i<rails) :
    image B rails g p m (B.cell+i) = (cellWord B p m i : Word W) := by
  have off : ¬B.touch≤B.cell+i := by omega
  simp [image,cellImage,fillSegment,hi,off]

theorem touch_at {W : ℕ} (B : Banks) (rails g p : ℕ) (m : Memory W)
    (i : ℕ) (hi : i<rails) :
    image B rails g p m (B.touch+i) = (touchWord B g p m i : Word W) := by
  simp [image,fillSegment,hi]

theorem frame {W : ℕ} (B : Banks) (rails g p : ℕ) (m : Memory W) (a : ℕ)
    (cell : a<B.cell ∨ B.cell+rails≤a) (touch : a<B.touch ∨ B.touch+rails≤a) :
    image B rails g p m a = m a := by
  have hc : ¬(B.cell≤a ∧ a<B.cell+rails) := by omega
  have ht : ¬(B.touch≤a ∧ a<B.touch+rails) := by omega
  simp [image,cellImage,fillSegment,hc,ht]

variable {W rails axes g p : ℕ} {B : Banks} (fit : Fits W B rails axes g p)
include fit

private theorem cell_exec (m : Memory W) :
    (PhysicalInputPhases.writing (HeaderScan.closed (cellExpr B p)) Fin.elim0 B.cell rails).Exec
      m (cellImage B rails p m) (4+rails*(2*(cellExpr B p).work+4)) := by
  have ⟨dc,cp,pt,td,stop,radix,pins⟩ := fit
  unfold cellImage
  rw [← HeaderScan.binds_closed (w:=W) (cellExpr B p)]
  intro P R K machine pc reg pub exit installed data cfg input start same
  subst input
  refine PhysicalInputPhases.writing_spec (HeaderScan.closed (cellExpr B p)) Fin.elim0 B.cell rails
    (by omega) (·=m) (fun a=>(cellWord B p m (a-B.cell) : Word W)) ?_
    machine pc reg pub exit installed data cfg m start rfl
  rintro _ rfl a o lo hi keep
  rw [HeaderScan.eval_closed]
  let i := a.val - B.cell
  have hi' : i<rails := by dsimp [i]; omega
  have addr : B.dest+2*i<2^W := by omega
  have read := keep (B.dest+2*i) (.inr (by omega))
  have fits : (cellExpr B p).Fits W (fun _=>0) (fun t=>(o t).val) (fun _=>a.val) := by
    simp only [cellExpr,loadAt,ordinalAt,Formula.Fits,Formula.natural,opFits,natOp,
      show a.val-B.cell=i from rfl,true_and,and_true]
    have av := a.isLt
    have dv := (o (B.dest+2*i)).isLt
    have cellFit : B.cell<2^W := by omega
    repeat' apply And.intro
    all_goals first | trivial
  have v := (cellExpr B p).value_eq_natural (w:=W) (fun _=>0) (fun t=>(o t).val) (fun _=>a.val) fits
  simp only [Nat.cast_zero,Fin.cast_val_eq_self] at v
  rw [v]
  change (((o (B.dest+2*i)).val/p : ℕ) : Word W) = _
  rw [read]
  rfl

private theorem touch_exec (m : Memory W) (dirRange : ∀ i<rails, (m (B.dir+i)).val < axes) :
    (PhysicalInputPhases.writing (HeaderScan.closed (touchExpr B g)) Fin.elim0 B.touch rails).Exec
      (cellImage B rails p m) (image B rails g p m) (4+rails*(2*(touchExpr B g).work+4)) := by
  have ⟨dc,cp,pt,td,stop,radix,pins⟩ := fit
  unfold image
  rw [← HeaderScan.binds_closed (w:=W) (touchExpr B g)]
  intro P R K machine pc reg pub exit installed data cfg input start same
  subst input
  refine PhysicalInputPhases.writing_spec (HeaderScan.closed (touchExpr B g)) Fin.elim0 B.touch rails
    (by omega) (·=cellImage B rails p m) (fun a=>(touchWord B g p m (a-B.touch) : Word W)) ?_
    machine pc reg pub exit installed data cfg (cellImage B rails p m) start rfl
  rintro _ rfl a o lo hi keep
  rw [HeaderScan.eval_closed]
  let i := a.val - B.touch
  have hi' : i<rails := by dsimp [i]; omega
  have dd : B.dir+i < B.cell := by omega
  have hd : o (B.dir+i) = m (B.dir+i) := by
    rw [keep _ (.inl (by omega))]
    simp [cellImage,fillSegment,Nat.not_le.mpr dd]
  have within := dirRange i hi'
  let j := (m (B.dir+i)).val
  have hj : j<axes := within
  have pp : B.power+j < B.touch := by omega
  have pout : ¬B.power+j < B.cell+rails := by omega
  have hp : o (B.power+j) = m (B.power+j) := by
    rw [keep _ (.inl pp)]
    simp [cellImage,fillSegment,pout]
  have cc : B.cell+i < B.touch := by omega
  have hc : o (B.cell+i) = (cellWord B p m i : Word W) := by
    rw [keep _ (.inl cc)]
    simp [cellImage,fillSegment,hi']
  have cellSmall : cellWord B p m i < 2^W :=
    (Nat.div_le_self ..).trans_lt (m (B.dest+2*i)).isLt
  have fits : (touchExpr B g).Fits W (fun _=>0) (fun t=>(o t).val) (fun _=>a.val) := by
    simp only [touchExpr,loadAt,ordinalAt,Formula.Fits,Formula.natural,opFits,natOp,
      show a.val-B.touch=i from rfl,hd,show (m (B.dir+i)).val=j from rfl,true_and,and_true]
    have av := a.isLt
    have cv := (o (B.cell+i)).isLt
    have pv := (o (B.power+j)).isLt
    have qv := Nat.div_le_self (o (B.cell+i)).val (o (B.power+j)).val
    have baseFit : B.touch<2^W := by omega
    have dirFit : B.dir+i<2^W := by omega
    have cellFit : B.cell+i<2^W := by omega
    have powFit : B.power+j<2^W := by omega
    repeat' apply And.intro
    all_goals first | trivial | omega
  have v := (touchExpr B g).value_eq_natural (w:=W) (fun _=>0) (fun t=>(o t).val) (fun _=>a.val) fits
  simp only [Nat.cast_zero,Fin.cast_val_eq_self] at v
  rw [v]
  change (((o (B.cell+i)).val / (o (B.power+(o (B.dir+i)).val)).val % g : ℕ) : Word W) = _
  rw [hd]
  change (((o (B.cell+i)).val / (o (B.power+j)).val % g : ℕ) : Word W) = _
  rw [hc,hp,Fin.val_cast_of_lt cellSmall]
  rfl

theorem execute (m : Memory W) (dirRange : ∀ i<rails, (m (B.dir+i)).val < axes) :
    (build W B rails g p).Exec m (image B rails g p m) (cost rails) := by
  have charge : (4+rails*(2*(cellExpr B p).work+4)) + (4+rails*(2*(touchExpr B g).work+4)) =
      cost rails := by simp [cost]; omega
  rw [←charge]
  intro P R K machine pc reg pub exit installed data cfg input start same
  exact Procedure.Exec.then (cell_exec fit m) (touch_exec fit m dirRange)
    machine pc reg pub exit installed data cfg input start same

end Hierarchy.GridSimRailScan

end OAI
