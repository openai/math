import OAI.Hierarchy.DescentTerminalHeaderScatter

namespace OAI
/-! # Physical publication of the two canonical packed chip input columns -/
namespace Hierarchy.DescentTerminalScatterChip
open DescentTerminalHeaderScatter DescentTerminalChipSource DescentTerminalScalarPadded
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  half : Bank
  lane : Bank
  live : Bank
  directory : Bank
  chunk : Bank
  publicMode : Bank
  owner : Bank
  siteFirst : Bank
  groupFirst : Bank
  sourceFirst : Bank
  privateWords : Bank
  publicWords : Bank

def event (L : Layout) : Expr := .lookup L.half .row
def group (L : Layout) : Expr := .lookup L.directory (event L)
def chunk (L : Layout) : Expr := .lookup L.chunk (event L)
def source (L : Layout) : Expr := .op .add (.lookup L.sourceFirst (group L)) (chunk L)
def target (L : Layout) : Expr := .op .add (.lookup L.siteFirst (.lookup L.owner (group L)))
  (.op .add (.lookup L.groupFirst (group L)) (chunk L))
def live (L : Layout) : Expr := .lookup L.live (event L)
def dest (L : Layout) (base sink : ℕ) : Expr := .branch .eq (live L) (.lit 0) (.lit sink) (.op .add (.lit base) (target L))
def datum (L : Layout) (offset : ℕ) : Expr := .branch .eq (live L) (.lit 0) (.lit 0)
  (.branch .eq (.lookup L.publicMode (group L)) (.lit 0) (.lookup L.privateWords (source L))
    (.op .add (.lit offset) (.lookup L.publicWords (source L))))

def program (bits base pool blank src events sink offset : ℕ) (L : Layout) :=
  (scan bits base pool (.lit blank)).seq (DescentTerminalHeaderScatter.program bits src events (dest L base sink) (datum L offset) L.lane)

def cost (pool events base sink offset : ℕ) (L : Layout) := (4+pool*(2*Expr.work (.lit 0)+4))+
  DescentTerminalHeaderScatter.cost events (dest L base sink) (datum L offset) L.lane

variable {n pool w : ℕ} {A : Type} (issued : Fin n→Option A) (atRow : A ↪ Fin pool)
    (key site pre start localR : A→ℕ) (onPublic : A→Bool) (ans : A→Word w)

structure Ranks (L : Layout) (m : Memory w) : Prop where
  half : ∀(i : Fin n) (j : Fin 2),L.half.read m ((field i j).val:Word w)=(i.val:Word w)
  lane : ∀(i : Fin n) (j : Fin 2),L.lane.read m ((field i j).val:Word w)=(j.val:Word w)
  active : ∀i : Fin n,L.live.read m (i.val:Word w)=((if (issued i).isSome then 1 else 0:ℕ):Word w)
  dir : ∀i a,issued i=some a→L.directory.read m (i.val:Word w)=(key a:Word w)
  slot : ∀i a,issued i=some a→L.chunk.read m (i.val:Word w)=(localR a:Word w)
  home : ∀a,L.owner.read m (key a:Word w)=(site a:Word w)
  groupFirst : ∀a,L.groupFirst.read m (key a:Word w)=(pre a:Word w)
  begin : ∀a,L.sourceFirst.read m (key a:Word w)=(start a:Word w)
  mode : ∀a,L.publicMode.read m (key a:Word w)=((if onPublic a then 1 else 0:ℕ):Word w)

structure Columns (L : Layout) (m : Memory w) (offset : ℕ) : Prop where
  place : ∀a,L.siteFirst.read m (site a:Word w)+((pre a+localR a:ℕ):Word w)=((atRow a).val:Word w)
  internal : ∀a,onPublic a=false→L.privateWords.read m (((start a+localR a:ℕ):Word w))=ans a
  exterior : ∀a,onPublic a=true→(offset:Word w)+L.publicWords.read m (((start a+localR a:ℕ):Word w))=ans a

def record (base sink : ℕ) (i : Fin n) : EffectStream.Record w :=
  match issued i with | none=>(sink,0) | some a=>((base+(atRow a).val:ℕ),ans a)

theorem record_read (L : Layout) (m : Memory w) (base sink offset : ℕ) (pos : 0<w)
    (r : Ranks issued key site pre start localR onPublic L m)
    (data : Columns atRow site pre start localR onPublic ans L m offset) (i : Fin n) (j : Fin 2) :
    (stage (dest L base sink) (datum L offset) L.lane).eval m ((field i j).val:Word w)=
      if j=0 then (record issued atRow ans base sink i).1 else (record issued atRow ans base sink i).2 := by
  rw [lane_read _ _ _ _ _ _ pos (r.lane i j)]
  have ne : (1:Word w)≠0:=by
    intro h
    have eq:=congrArg Fin.val h
    simp at eq
    omega
  cases z:issued i with
  | none=>by_cases j=0 <;> simp [*,dest,datum,live,event,record,Expr.eval,Comparison.test,r.half,r.active]
  | some a=>
    by_cases side:j=0
    · simp [side,dest,live,event,record,Expr.eval,Comparison.test,r.half,r.active,z,ne,target,group,chunk,r.dir i a z,
        r.home,r.slot i a z,r.groupFirst,RowOp.opcode,BinaryOp.eval,Nat.cast_add] at *
      simpa [Nat.cast_add] using congrArg ((base:Word w)+·) (data.place a)
    · cases on : onPublic a <;>
        simp [side,datum,live,event,record,Expr.eval,Comparison.test,r.half,r.active,z,ne,group,chunk,r.dir i a z,
          r.slot i a z,source,r.begin,r.mode,on,RowOp.opcode,BinaryOp.eval,←Nat.cast_add,data.internal,data.exterior]

section Execution

attribute [local irreducible] Procedure.Exec CheapCode

private theorem native_issue (L : Layout) (base sink src blank offset : ℕ)
    (m clear final : Memory w)
    (first : (scan w base pool (.lit blank)).Exec m clear (4+pool*(2*Expr.work (.lit blank)+4)))
    (second : (DescentTerminalHeaderScatter.program w src n (dest L base sink) (datum L offset) L.lane).Exec
      clear final (DescentTerminalHeaderScatter.cost n (dest L base sink) (datum L offset) L.lane))
    (cheap : CheapCode (DescentTerminalHeaderScatter.program w src n (dest L base sink) (datum L offset) L.lane)) :
    (program w base pool blank src n sink offset L).Exec m final (cost pool n base sink offset L) ∧
      CheapCode (program w base pool blank src n sink offset L) := by
  let wipe := scan w base pool (.lit blank)
  let write := DescentTerminalHeaderScatter.program w src n (dest L base sink) (datum L offset) L.lane
  exact ⟨@Procedure.Exec.then w wipe write m clear final (4+pool*(2*Expr.work (.lit blank)+4))
    (DescentTerminalHeaderScatter.cost n (dest L base sink) (datum L offset) L.lane) (@first) (@second),
    @cheap_seq w wipe write (@scan_cheap w base pool (.lit blank)) (@cheap)⟩

private theorem published_rows (before : Memory w) (base sink blank : ℕ)
    (hole : ∀ k, issued k = none → (record issued atRow ans base sink k).1.val = sink)
    (address : ∀ k a, issued k = some a → (record issued atRow ans base sink k).1.val = base + (atRow a).val)
    (cover : ∀ a, ∃ i, issued i = some a) (sinkAway : base + pool ≤ sink)
    (initial : ∀ i : Fin pool, before (base+i.val) = (blank : Word w)) (i : Fin pool) :
    after before (EffectStream.events (List.ofFn (record issued atRow ans base sink))) (base+i.val) =
      Function.extend atRow ans (fun _ => (blank : Word w)) i := by
  apply published before (record issued atRow ans base sink) (base+i.val)
    (Function.extend atRow ans (fun _ => (blank : Word w)) i)
  · intro k hit
    cases z : issued k with
    | none =>
      have eq := (hole k z).symm.trans hit
      have hi := i.isLt
      omega
    | some a =>
      have eq : atRow a = i := Fin.ext (Nat.add_left_cancel ((address k a z).symm.trans hit))
      rw [←eq, atRow.injective.extend_apply]
      simp only [record, z]
  · by_cases live : ∃a, atRow a=i
    · obtain ⟨a, rfl⟩ := live
      obtain ⟨k, hit⟩ := cover a
      exact Or.inr ⟨k, address k a hit⟩
    · left
      rw [Function.extend_apply' ans (fun _ => (blank : Word w)) i live]
      exact initial i

set_option maxHeartbeats 1200000 in
theorem run (L : Layout) (m : Memory w) (base sink src blank offset : ℕ) (pos : 0<w)
    (r : Ranks issued key site pre start localR onPublic L m) (data : Columns atRow site pre start localR onPublic ans L m offset)
    (cover : ∀a,∃i,issued i=some a) (sinkAway : base+pool ≤ sink) (sinkFits : sink<src)
    (exprFit : (stage (dest L base sink) (datum L offset) L.lane).Fits w base)
    (later : (stage (dest L base sink) (datum L offset) L.lane).Fits w src) (room : src+2*n<2^w) :
    let e:=stage (dest L base sink) (datum L offset) L.lane
    let startMem:=image base pool (.lit blank) m
    let before:=image src (2*n) e startMem
    let afterMem:=after before (EffectStream.events (List.ofFn (record issued atRow ans base sink)))
    (program w base pool blank src n sink offset L).Exec m afterMem (cost pool n base sink offset L) ∧
      CheapCode (program w base pool blank src n sink offset L) ∧
      ∀i : Fin pool,afterMem (base+i.val)=Function.extend atRow ans (fun _=>(blank:Word w)) i := by
  intro e startMem before afterMem
  have cleared := @scan_exec w base pool (.lit blank) m trivial (by omega)
  have small (a : A) : base+(atRow a).val<src:=by have:=(atRow a).isLt;omega
  have srcFit : src < 2^w := by omega
  have hole (k : Fin n) (missing : issued k = none) :
      (record issued atRow ans base sink k).1.val = sink := by
    simpa only [record, missing] using (Fin.val_cast_of_lt (sinkFits.trans srcFit))
  have address (k : Fin n) (a : A) (assigned : issued k = some a) :
      (record issued atRow ans base sink k).1.val = base + (atRow a).val := by
    simpa only [record, assigned] using (Fin.val_cast_of_lt ((small a).trans srcFit))
  have safe (i : Fin n) : (record issued atRow ans base sink i).1.val<src ∨ src+2*n≤(record issued atRow ans base sink i).1.val := by
    left
    cases h : issued i with
    | none => exact (hole i h).trans_lt sinkFits
    | some a => exact (address i a h).trans_lt (small a)
  have eqn (i : Fin n) (j : Fin 2) : e.eval startMem ((field i j).val:Word w) =
      if j = 0 then (record issued atRow ans base sink i).1 else (record issued atRow ans base sink i).2 :=
    (eval_below e _ m startMem exprFit (fun _ h => DescentTerminalChipRuntime.image_low m base pool (.lit blank) h)).trans
      (record_read issued atRow key site pre start localR onPublic ans L m base sink offset pos r data i j)
  obtain ⟨scatter,cheap⟩:=DescentTerminalHeaderScatter.emit (dest L base sink) (datum L offset) L.lane
    startMem src (record issued atRow ans base sink) later room safe eqn
  have native := native_issue (pool:=pool) (n:=n) L base sink src blank offset m startMem afterMem
    (@cleared) (@scatter) (@cheap)
  refine ⟨native.1, native.2, published_rows issued atRow ans before base sink blank hole address cover sinkAway ?_⟩
  intro i
  have h : base + i.val < src := by have := i.isLt; omega
  exact (DescentTerminalChipRuntime.image_low startMem src (2*n) e h).trans
    (DescentTerminalChipRuntime.image_at m base pool (.lit blank) i)

end Execution

end
end Hierarchy.DescentTerminalScatterChip

end OAI
