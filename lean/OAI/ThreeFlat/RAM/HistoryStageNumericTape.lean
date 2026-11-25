import OAI.ThreeFlat.RAM.HistoryStageTypedRows
import OAI.ThreeFlat.RAM.HistoryStageBankArena

namespace OAI
/-! # Numeric operands of a selected stage after a relabeling of its old chart -/
namespace ThreeFlat.RAM.HistoryStageNumericTape
open Computability.VPVNP.BurstRAM PrivateRAM BitLayout Diagonal.HistoryContraction
open HistoryStageRoot HistoryStageBody HistoryBoundedBody HistoryBoundedJoin
open HistoryPartyBatchExec HistoryStageSnapshots
open scoped BigOperators Fin.CommRing
noncomputable section
variable {F : Type*} {W h p n : ℕ} {arity : Fin n→ℕ}
variable (T : Input) (raw : ℕ→ℕ) (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (tag : ((Fin 3→Bool)→F)→ℕ)
/-- The six natural-valued header fields also apply to networks over higher universes. -/
private abbrev copyHeader {F : Type*} {n h p : ℕ} {ar : Fin n→ℕ}
    (T : Input) (raw : ℕ→ℕ) (N : ∀ i,BitNetwork F (ar i))
    (_ : ∀ i,Fin (ar i)→BitSource h p) (i : Fin n) : HistoryJoinScan.Header ℕ :=
  ⟨(atResult raw (ptr T raw i.val)).stream,T.stream+4*Tree.before (fun j=>(N j).cells) i,
    mapPtr T raw i.val,ar i,p,h+Tree.before (fun j=>(N j).internal) i⟩

private theorem copyHeader_typed {F : Type} {n h p : ℕ} {ar : Fin n→ℕ}
    (T : Input) (raw : ℕ→ℕ) (N : ∀ i,BitNetwork F (ar i))
    (wire : ∀ i,Fin (ar i)→BitSource h p) (i : Fin n) :
    copyHeader T raw N wire i=Typed.copy T raw N wire i := rfl

local notation "q" => copyHeader T raw N wire
local notation "H" => HistoryStageRoot.hub T raw
local notation "mapping" => Typed.mapRow T raw

/-- Only numeric operand identities are used to execute the row emitter. The tree
itself stays in its actual chart, with its actual ordered children and local kernel. -/
structure Wiring : Prop where
  size : n=childCount T raw+1
  pins : outPins T raw=p
  shared : hidden T raw=h
  source : ∀ i,∀ j : Fin (arity i),sourceAddress (wire i j)=
    HistoryPortMap.piecewise j.val (operands T raw i.val 2) (operands T raw i.val 3) (operands T raw i.val 4)

structure Stored (mem : Memory W) : Prop where
  info : ∀ i,Typed.infoAt T raw i.val=
    ⟨(q i).source,arity i,(N i).cells,(N i).internal⟩
  rows : ∀ i,HistoryCompiledRows.Records tag (N i) (q i).source mem

structure Readback (mem : Memory W) : Prop where
  child : ∀ i : Fin n,child H (numeric mem) i.val=HistoryStageRoot.link T raw i.val
  info : ∀ i : Fin n,read (ptr T raw i.val) (numeric mem)=Typed.infoAt T raw i.val

variable {T raw N wire tag}
theorem readback (A : HistoryGatherBody.Layout) (cap : ℕ) (mem : Memory W)
    (shape : Wiring T raw wire) (s : Snapshot A cap T raw mem) (c : CachedInfo T raw mem)
    (atLinks : T.links=links A) (fit : ∀ i : Fin n,∀ j,(HistoryStageRoot.link T raw i.val).words j<2^W) :
    Readback (n:=n) T raw mem := by
  have ix (i : Fin n) : i.val<childCount T raw+1:=by rw [←shape.size];exact i.isLt
  exact ⟨fun i=>s.readChild atLinks ⟨i.val,ix i⟩ (fit i),fun i=>c ⟨i.val,ix i⟩⟩

variable {mem orig : Memory W}
theorem decoded (s : Stored T raw N wire tag orig) (r : Readback (n:=n) T raw mem) (i : Fin n) :
    read (child H (numeric mem) i.val).node (numeric mem)=
      ⟨(q i).source,arity i,(N i).cells,(N i).internal⟩ := by
  rw [r.child i];exact (r.info i).trans (s.info i)

theorem position (g : Wiring T raw wire) (s : Stored T raw N wire tag orig)
    (r : Readback (n:=n) T raw mem) (i : Fin n) :
    moved H (numeric mem) i.val=(q i).dest ∧ offset H (numeric mem) i.val=(q i).offset := by
  apply moved_eq N wire H (numeric mem) i g.shared
  intro j;rw [decoded s r j]

theorem commandWords (g : Wiring T raw wire) (s : Stored T raw N wire tag orig)
    (r : Readback (n:=n) T raw mem) (i : Fin n) :
    command H (numeric mem) i.val false=
      ![(Typed.mapRow T raw i.val).arg,(q i).pins,8,0,0,0,(q i).pins+arity i] ∧
    command H (numeric mem) i.val true=
      ![(H).arguments+7*i.val,(q i).dest,1,0,0,0,(q i).dest+4*(N i).cells] := by
  obtain ⟨dst,_⟩:=position g s r i
  have actual := decoded s r i
  rw [r.child i] at actual
  constructor <;> simp only [command,Bool.false_eq_true,ite_false,ite_true,r.child i,actual,dst]; rfl

theorem copyWords (g : Wiring T raw wire) (s : Stored T raw N wire tag orig)
    (r : Readback (n:=n) T raw mem) (i : Fin n) (j : Fin 6) :
    arguments H (numeric mem) i.val j.castSucc=
      (![(q i).source,(q i).dest,(q i).pins,(q i).oldPins,(q i).newPins,(q i).offset] j) := by
  obtain ⟨dst,off⟩:=position g s r i
  dsimp only [HistoryBoundedJoin.arguments]
  rw [decoded s r i,r.child i,dst,off]
  fin_cases j <;> first | rfl | exact g.pins

theorem mapWords (s : Stored T raw N wire tag orig) (i : Fin n) (j : Fin 5) :
    operands T raw i.val j=
      (![(q i).pins,arity i,(mapping i.val).split,(mapping i.val).first,(mapping i.val).second] j) := by
  have sz:=congrArg Info.pins (s.info i)
  change (atResult raw (ptr T raw i.val)).pins=arity i at sz
  fin_cases j
  · by_cases z : i.val=0 <;> simp [operands,mapPtr,z]
  · unfold operands
    split <;> exact sz
  · rfl
  · rfl
  · rfl

theorem mapValue (g : Wiring T raw wire) (mem : Memory W) (i : Fin n) (j : Fin (arity i)) :
    (mapping i.val).value mem j.val=(sourceAddress (wire i j):Word W) :=
  congrArg (fun x : ℕ=>(x:Word W)) (g.source i j).symm


end
end ThreeFlat.RAM.HistoryStageNumericTape

end OAI
