import OAI.Hierarchy.ProbeReportSockets
import OAI.Hierarchy.ProtocolRAMSupergroupDirectory
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Native lookup and addressing for the reported stage sockets -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMGeneratedWrite TaggedShorterSupergroups
open scoped Fin.CommRing Classical

private theorem scaleFits {w base : ℕ} (e : Expr) (fit : e.Fits w base) (c : ℕ) :
    (scale c e).Fits w base := by
  induction c with
  | zero => trivial
  | succ c ih => exact ⟨fit,ih⟩

/-- The group offset ROM already contains its base multiplied by the public
lane width. Every multiplication below is by a format constant. -/
def addressExpr (copies lanes : ℕ) (offsets : Bank) (group port tag : Expr) : Expr :=
  .op .add (.lookup offsets group) (scale lanes (.op .add tag (scale copies port)))

variable {w h W k attempts K H N : ℕ}

def portProgram (w N start K groupOut baseOut copies lanes : ℕ) (group port tag : Expr) :=
  (scan w groupOut N (.lookup (ProtocolRAMSupergroupDirectory.groupBank start K) group)).seq
    (scan w baseOut N (addressExpr copies lanes (ProtocolRAMSupergroupDirectory.offsetBank start K)
      group port tag))

def portImage (N start K groupOut baseOut copies lanes : ℕ) (group port tag : Expr) (mem : Memory w) :=
  ProtocolRAM.image baseOut N (addressExpr copies lanes (ProtocolRAMSupergroupDirectory.offsetBank start K)
    group port tag) (ProtocolRAM.image groupOut N (.lookup (ProtocolRAMSupergroupDirectory.groupBank start K) group) mem)

def portWork (N start K copies lanes : ℕ) (group port tag : Expr) :=
  (4+N*(2*(Expr.lookup (ProtocolRAMSupergroupDirectory.groupBank start K) group).work+4))+
    (4+N*(2*(addressExpr copies lanes (ProtocolRAMSupergroupDirectory.offsetBank start K) group port tag).work+4))

open ProtocolRAMSupergroupDirectory in
theorem execute (start groupOut baseOut copies lanes : ℕ) (group port tag : Expr) (mem : Memory w)
    (gf : (groupBank start K).Fits w groupOut) (ofit : (offsetBank start K).Fits w groupOut)
    (gfit : group.Fits w groupOut) (pfit : port.Fits w groupOut) (tfit : tag.Fits w groupOut)
    (apart : groupOut+N≤baseOut) (fit : baseOut+N<2^w) :
    (portProgram w N start K groupOut baseOut copies lanes group port tag).Exec mem
      (portImage N start K groupOut baseOut copies lanes group port tag mem)
      (portWork N start K copies lanes group port tag) := by
  let first := ProtocolRAM.image groupOut N (.lookup (groupBank start K) group) mem
  let addr := addressExpr copies lanes (offsetBank start K) group port tag
  have fits : addr.Fits w groupOut :=
    ⟨⟨ofit,gfit⟩,scaleFits (.op .add tag (scale copies port)) ⟨tfit,scaleFits port pfit copies⟩ lanes⟩
  let query := Expr.lookup (groupBank start K) group
  have one : (scan w groupOut N query).Exec mem first (4+N*(2*query.work+4)) :=
    scan_exec groupOut N query mem ⟨gf,gfit⟩ (by omega)
  have two : (scan w baseOut N addr).Exec first (ProtocolRAM.image baseOut N addr first)
      (4+N*(2*addr.work+4)) :=
    scan_exec baseOut N addr first (fits_mono _ (by omega : groupOut≤baseOut) fits) fit
  intro P R K' M pc reg pub exit installed data cfg raw entry eq
  exact Procedure.Exec.then one two M pc reg pub exit installed data cfg raw entry eq

open ProtocolRAMSupergroupDirectory in
theorem read (start groupOut baseOut lanes : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (group port tag : Expr) (mem : Memory w)
    (whereAt : Fin N → StageColumns h (2^W) × Role k attempts) (ids : K≤2^w)
    (ofit : (offsetBank start K).Fits w groupOut) (gfit : group.Fits w groupOut)
    (pfit : port.Fits w groupOut) (tfit : tag.Fits w groupOut) (apart : groupOut+N≤baseOut)
    (groupData : ∀ i,group.eval (mount start lanes groups dir mem) (i.val:Word w) =
      ((groups.symm (owner (whereAt i).1)).val:Word w))
    (portData : ∀ i,port.eval (mount start lanes groups dir mem) (i.val:Word w) =
      ((socketPort (whereAt i).1).val:Word w))
    (tagData : ∀ i,tag.eval (mount start lanes groups dir mem) (i.val:Word w) =
      ((socketTag (whereAt i).1 (whereAt i).2).val:Word w)) (i : Fin N) :
    let result := portImage N start K groupOut baseOut (copies k attempts) lanes group port tag
      (mount start lanes groups dir mem)
    result (groupOut+i.val)=((packed dir (whereAt i)).1.val:Word w) ∧
      result (baseOut+i.val)=(((packed dir (whereAt i)).2.val*lanes:ℕ):Word w) := by
  intro result
  let initial := mount start lanes groups dir mem
  let query := Expr.lookup (groupBank start K) group
  let first := ProtocolRAM.image groupOut N query initial
  let addr := addressExpr (copies k attempts) lanes (offsetBank start K) group port tag
  have fits : addr.Fits w groupOut :=
    ⟨⟨ofit,gfit⟩,scaleFits (.op .add tag (scale (copies k attempts) port))
      ⟨tfit,scaleFits port pfit (copies k attempts)⟩ lanes⟩
  have bank := resident start lanes groups dir mem ids (owner (whereAt i).1)
  constructor
  · change ProtocolRAM.image baseOut N addr first (groupOut+i.val)=_
    rw [frame_image _ _ _ _ _ (Or.inl ((Nat.add_lt_add_left i.isLt _).trans_le apart)),
      show first (groupOut+i.val)=query.eval initial (i.val:Word w) from read_image ..]
    change (groupBank start K).read initial (group.eval initial (i.val:Word w))=_
    rw [show group.eval initial (i.val:Word w)=_ from groupData i]
    exact bank.1
  · change ProtocolRAM.image baseOut N addr first (baseOut+i.val)=_
    rw [read_image,eval_below addr _ initial first fits (fun j hj=>frame_image _ _ _ _ j (Or.inl hj))]
    change (addressExpr (copies k attempts) lanes (offsetBank start K) group port tag).eval
      (mount start lanes groups dir mem) (i.val:Word w)=_
    simp only [addressExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,eval_scale,groupData,portData,tagData,bank.2]
    change _=(((dir.base (owner (whereAt i).1)+(offset (whereAt i).1 (whereAt i).2).val)*lanes:ℕ):Word w)
    rw [offset_val]
    push_cast
    ring

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
