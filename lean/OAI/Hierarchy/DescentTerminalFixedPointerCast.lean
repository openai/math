import OAI.Hierarchy.DescentTerminalPointerIssue

namespace OAI
/-! # Fixed scalar lookup dimensions on an attained branch -/
namespace Hierarchy.DescentTerminalPointerIssue
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentTerminalBoundaryBasis DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks
open ThreeFlat.Routing DescentTerminalVertexFields
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Reindex the physical gather columns according to the reached stage capacity. -/
def sourceAtCapacity {c e N M d:ℕ} (same:c=e) (row:Source c N M d) : Source e N M d := same ▸ row

/-- Express the genuine original inputs in the reached lookup's physical dimensions. -/
def inputsAtShape {D E c e N M:ℕ} (degree:D=E) (slots:c=e) (t:CellInputs D c N M) : CellInputs E e N M :=
  degree ▸ slots ▸ t

theorem read_at_capacity {D E c e N M d g:ℕ} (degree:D=E) (slots:c=e) (s:Widths)
    (row:Source e N M d) (t:CellInputs D c N M)
    (read:SourceRead s row g (inputsAtShape degree slots t)) :
    SourceRead s (sourceAtCapacity slots.symm row) g t := by
  subst E;subst e;exact read

theorem column_at_capacity {c e N M d:ℕ} (slots:c=e) (row:Source e N M d) :
    (sourceAtCapacity slots.symm row mcol).val=(row mcol).val ∧
    (sourceAtCapacity slots.symm row fcol).val=(row fcol).val := by
  subst e;exact ⟨rfl,rfl⟩

theorem argument_at_capacity {D E c e N M d:ℕ} (degree:D=E) (slots:c=e)
    (s:Widths) (index:ℕ→ℕ→ℕ→ℕ) (row:Source e N M d) (g q scale psize:ℕ) (i:Fin (N*M)) :
    (decode E s index row g).argument q scale psize i=
    (decode D s index (sourceAtCapacity slots.symm row) g).argument q scale psize i := by
  subst E;subst e;rfl

/-- The masked family-six shelf exposes the same per-node arity digit used by
the argument lookup on the unmasked physical word. -/
theorem native_arity_digit {q tags H N A p groups blocks hosts wb:ℕ}
    (machine:MaskedShelf blocks) (m:Memory wb) (base:ℕ) (b:Fin blocks)
    (placed:(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).base=base)
    (size:hosts≤(machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).size)
    (word:hosts≤2^wb) (h:Fin hosts) (g:Fin groups) (u:Fin N) :
    venueField (cellAt (measured (q:=q) (t:=tags) (H:=H) (N:=N) (A:=A) (w:=p)
      (groups:=groups) machine m h) (finProdFinEquiv (g,b))) (nodeArity u)=
      digit (Nat.clog 2 (A+1)) u.val (digit (Nat.clog 2 (A+1)*N) g.val (m (base+h.val)).val) := by
  let bytes:=Nat.clog 2 (A+1)
  rw [venue_digit]
  change digit bytes u.val ((cellAt (measured (q:=q) (t:=tags) (H:=H) (N:=N) (A:=A) (w:=p)
    (groups:=groups) machine m h) (finProdFinEquiv (g,b))) 6).val=_
  rw [cell_digit,measured_channel]
  change digit bytes u.val (digit (N*bytes) g.val
    (((machine.channel (finProdFinEquiv (b,(6:Fin 8).succ))).read m (h.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^(N*bytes*groups)))=_
  rw [digit_clip,Nat.mul_comm N bytes,Bank.read,Fin.val_cast_of_lt (h.isLt.trans_le word),
    Nat.mod_eq_of_lt (h.isLt.trans_le size),placed]

section Rows

variable {Tag B:Type} {D c N M d:ℕ} (r:Recipe Tag B) (birth:r.Node↪ℕ)
    (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M)
    (operand:Slot r→Pointer) (wings:Fin (2*c)→Option (Stage.Live D c))
local notation "nr" => row r birth nodes
local notation "where_" => slot r birth nodes arity

private theorem row_inj : Function.Injective (row r birth nodes) := by
  intro u v equal
  have pos: (nr u).val=(nr v).val:=congrArg (fun j:Fin N=>j.val) equal
  exact (ordinal birth).injective (Fin.ext pos)

/-- The genuine sparse node and operand coordinates determine a rectangular input.
Only addresses that belong to the original recipe have an operand interpretation. -/
def issuedInputs : CellInputs D c N M where
  n:=Fintype.card r.Node
  arity:=Function.extend nr r.arity (fun _=>0)
  pointer:=Function.extend where_ operand (fun _=>.privateWord 0)
  chips:=wings

local notation "t_" => issuedInputs r birth nodes arity operand wings
/-- Transport only the signed panel when the reached degree/capacity is identified
with the fixed ROM. The pointer rectangle and population coordinate stay literal. -/
def wingsAtShape {D' c':ℕ} (degree:D=D') (slots:c=c') (panel:Fin (2*c)→Option (Stage.Live D c)) :
    Fin (2*c')→Option (Stage.Live D' c') := by
  subst D';subst c';exact panel

theorem issued_at_shape {D' c':ℕ} (degree:D=D') (slots:c=c') :
    inputsAtShape degree slots t_ = issuedInputs r birth nodes arity operand (wingsAtShape degree slots wings) := by
  subst D';subst c';rfl

theorem issued_arity (u:r.Node) : (issuedInputs r birth nodes arity operand wings).arity (nr u)=r.arity u := by
  change Function.extend (row r birth nodes) r.arity (fun _ => 0) (row r birth nodes u) = r.arity u
  exact (row_inj r birth nodes).extend_apply r.arity (fun _ => 0) u
theorem issued_pointer (s:Slot r) : (issuedInputs r birth nodes arity operand wings).pointer (where_ s)=operand s := by
  change Function.extend (slot r birth nodes arity) operand (fun _ => .privateWord 0)
    (slot r birth nodes arity s) = operand s
  exact (slot r birth nodes arity).injective.extend_apply operand (fun _ => .privateWord 0) s

/-- Authenticate the four pointer fields only at actual archived arguments. The
padded addresses never need to carry any particular pointer tag or payload. -/
theorem issued_read (fmt:Widths) (source:Source c N M d) (grp:ℕ)
    (population:digit fmt.nodes grp (source ncol).val=Fintype.card r.Node)
    (widths:∀u:r.Node,fmt.nodeDigit fmt.arity (nr u).val grp (source (acol (nr u))).val=r.arity u)
    (fields:∀(a:Slot r) (f:Fin 4),fmt.nodeDigit (fmt.pointer f) (nodeOf (where_ a)).val grp
      (source (pcol f (where_ a))).val=(operand a).header f)
    (side:∀j:Fin (2*c),DescentSignedCableCodec.decode D c
      ((digit (DescentSignedCableCodec.width D c) grp (source (scol j)).val:ℕ):Cell _)=wings j) :
    SourceRead fmt source grp t_ := by
  refine ⟨population,?_,?_,side⟩
  · intro i hi
    let name:Fin (Fintype.card r.Node):=⟨i.val,hi⟩
    let u:=(ordinal birth).symm name
    have valAt:(ordinal birth u).val=name.val:=
      congrArg (fun j:Fin (Fintype.card r.Node)=>j.val) ((ordinal birth).apply_symm_apply name)
    have atRow:nr u=i:=Fin.ext valAt
    rw [←atRow,issued_arity]
    exact widths u
  · intro i on f
    obtain ⟨a,rfl⟩ : ∃a:Slot r,where_ a=i := by
      apply Classical.byContradiction
      intro missing
      exact inactive r birth nodes arity t_ rfl (issued_arity r birth nodes arity operand wings) i
        (fun a equal=>missing ⟨a,equal⟩) on
    rw [issued_pointer]
    exact fields a f

end Rows

section Reached
variable {F P J V Tag : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p q N M K tags : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ) (v:W.graph.Site) (coords:Function.Injective (fun s=>(A.pos s,A.block s)))
    (port:Attached W.graph v↪ℕ) (hp:0<p) (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀z:Attached W.graph v,poolBatchCount (bits z.val) p=psize)
    (r:Recipe Tag (BlockRef p (boundaryWidth W.graph v))) (code:Tag→Fin tags)
    (birth:r.Node↪ℕ) (nodes:Fintype.card r.Node≤N) (arity:∀u,r.arity u≤M) (aliases:Slot r↪Fin K)
    (t:CellInputs A.degree A.cap N M)
local notation "rk" => rank A native S ready names v port
local notation "loc" => slot r birth nodes arity
local notation "chart" => Function.Embedding.trans (firstAlias r aliases) Fin.valEmbedding
local notation "G'" => W.graph
local notation "sparse" => Origin G' v r birth nodes arity aliases rk port t
local notation "sig" => Stage.signedPanel A native S ready names (Stage.home A v)


include coords whole common in
theorem reached_fixed_argument {D slots₀ d0:ℕ} (degree:A.degree=D) (capacity:A.cap=slots₀)
    (config:Widths) (raw:Source slots₀ N M d0) (g:ℕ) (index:ℕ→ℕ→ℕ→ℕ)
    (read:SourceRead config raw g (inputsAtShape degree capacity t))
    (origin:Origin G' v r birth nodes arity aliases rk port (reindexed t (index (raw mcol).val (raw fcol).val)))
    (chips:t.chips=sig) (u:r.Node) (j:Fin (r.arity u)) :
    (decode D config index raw g).argument q scale psize (loc ⟨u,j⟩)=
      DescentTerminalBoundaryPointer.num (q:=q) G' hp v rk r code chart u j := by
  have from_:=read_at_capacity degree capacity config raw t read
  have cells:=column_at_capacity capacity raw
  rw [argument_at_capacity degree capacity config index raw]
  exact reached_argument A native S ready names v coords port hp scale psize whole common r code birth nodes arity
    aliases t config (sourceAtCapacity capacity.symm raw) g index from_ (by simpa only [cells.1,cells.2] using origin)
    chips u j

end Reached
end
end Hierarchy.DescentTerminalPointerIssue

end OAI
