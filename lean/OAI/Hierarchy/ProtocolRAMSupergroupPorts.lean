import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Reindexing an actual physical port reservation into its fixed supergroup -/

namespace Hierarchy.ProtocolRAMSupergroupPorts

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Fin.CommRing

variable {W N lanes : ℕ} {G : Type*}

def groupExpr (groups : Bank) (old : Expr) : Expr := .lookup groups old

def baseExpr (offsets localBase : Bank) (old : Expr) : Expr :=
  .op .add (.lookup offsets old) (.lookup localBase .row)

/-- The two output columns are dense in the original row ordinal. All directory lookups
are one-dimensional and independent of which incident rows are active. -/
def program (W N groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) :=
  (scan W groupOut N (groupExpr groups old)).seq (scan W baseOut N (baseExpr offsets localBase old))

def work (N : ℕ) (old : Expr) :=
  (4+N*(2*(old.work+5)+4))+(4+N*(2*(old.work+13)+4))

def image (N groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) (mem : Memory W) :=
  ProtocolRAM.image baseOut N (baseExpr offsets localBase old)
    (ProtocolRAM.image groupOut N (groupExpr groups old) mem)

theorem run (groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) (mem : Memory W)
    (low : old.Fits W groupOut) (gf : groups.Fits W groupOut)
    (bf : offsets.Fits W groupOut) (lf : localBase.Fits W groupOut)
    (sep : groupOut+N≤baseOut) (fit : baseOut+N<2^W) :
    (program W N groupOut baseOut groups offsets localBase old).Exec mem
      (image N groupOut baseOut groups offsets localBase old mem) (work N old) := by
  have egroup : (groupExpr groups old).Fits W groupOut := ⟨gf,low⟩
  have ebase : (baseExpr offsets localBase old).Fits W groupOut := ⟨⟨bf,low⟩,⟨lf,trivial⟩⟩
  have a : (scan W groupOut N (groupExpr groups old)).Exec mem _
      (4+N*(2*(groupExpr groups old).work+4)) := scan_exec groupOut N (groupExpr groups old) mem egroup (by omega)
  have b : (scan W baseOut N (baseExpr offsets localBase old)).Exec _ _
      (4+N*(2*(baseExpr offsets localBase old).work+4)) :=
    scan_exec baseOut N _ (ProtocolRAM.image groupOut N (groupExpr groups old) mem)
      (fits_mono (baseExpr offsets localBase old) (by omega : groupOut≤baseOut) ebase) fit
  have baseWork : (baseExpr offsets localBase old).work=old.work+13 := by
    simp only [baseExpr,Expr.work]
  change ( (scan W groupOut N (groupExpr groups old)).seq (scan W baseOut N (baseExpr offsets localBase old))).Exec
    mem _ _
  have clock : (4+N*(2*(groupExpr groups old).work+4))+(4+N*(2*(baseExpr offsets localBase old).work+4))=
      work N old := by simp only [work,baseWork,groupExpr,Expr.work]
  rw [←clock]
  intro P R K M pc reg pub exit installed data cfg raw entry eq
  exact Procedure.Exec.then a b M pc reg pub exit installed data cfg raw entry eq

theorem frame (groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) (mem : Memory W)
    (a : ℕ) (ng : a<groupOut ∨ groupOut+N≤a) (nb : a<baseOut ∨ baseOut+N≤a) :
    image N groupOut baseOut groups offsets localBase old mem a=mem a :=
  (frame_image baseOut N _ _ a nb).trans (frame_image groupOut N _ _ a ng)

/-- Both words are read from the same original physical row, using fixed ROMs for
the supergroup number and the reserved prefix multiplied by the immutable lane count. -/
theorem read (groupOut baseOut : ℕ) (groups offsets localBase : Bank) (old : Expr) (mem : Memory W)
    (key : G→ℕ) (owner : Fin N→G) (newGroup base : G→ℕ) (localPort : Fin N→ℕ)
    (low : old.Fits W groupOut) (bf : offsets.Fits W groupOut) (lf : localBase.Fits W groupOut)
    (sep : groupOut+N≤baseOut)
    (oldData : ∀ i,old.eval mem (i.val:Word W)=(key (owner i):Word W))
    (groupData : ∀ g,groups.read mem (key g:Word W)=(newGroup g:Word W))
    (offsetData : ∀ g,offsets.read mem (key g:Word W)=((base g*lanes:ℕ):Word W))
    (baseData : ∀ i,localBase.read mem (i.val:Word W)=((localPort i*lanes:ℕ):Word W))
    (i : Fin N) :
    let result := image N groupOut baseOut groups offsets localBase old mem
    result (groupOut+i.val)=(newGroup (owner i):Word W) ∧
      result (baseOut+i.val)=(((base (owner i)+localPort i)*lanes:ℕ):Word W) := by
  intro result
  let first := ProtocolRAM.image groupOut N (groupExpr groups old) mem
  constructor
  · have keeps := frame_image baseOut N (baseExpr offsets localBase old) first (groupOut+i.val)
      (Or.inl ((Nat.add_lt_add_left i.isLt _).trans_le sep))
    rw [show result (groupOut+i.val)=first (groupOut+i.val) from keeps,
      show first (groupOut+i.val)=(groupExpr groups old).eval mem (i.val:Word W) from read_image ..]
    exact (congrArg (groups.read mem) (oldData i)).trans (groupData _)
  · rw [show result (baseOut+i.val)=(baseExpr offsets localBase old).eval first (i.val:Word W) from read_image ..,
      eval_below (baseExpr offsets localBase old) (i.val:Word W) mem first ⟨⟨bf,low⟩,lf,trivial⟩
        (fun j hj=>frame_image groupOut N _ mem j (Or.inl hj))]
    simp only [baseExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,oldData,offsetData,baseData,Nat.add_mul,Nat.cast_add]


end Hierarchy.ProtocolRAMSupergroupPorts

end OAI
