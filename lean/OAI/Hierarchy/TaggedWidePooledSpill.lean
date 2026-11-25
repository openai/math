import OAI.Hierarchy.TaggedWideSpillAperture
import OAI.Hierarchy.TaggedWidePhysicalSpill

namespace OAI
/-! # Fixed turn comparator for a dated commodity spill with local output states -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.Mount
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged WireTelescope Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F : Type*} [Field F] {S : PurchaseSampler} {h d k K edges r W N p e slots : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)
    (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
local notation "L" => B.datedLayout inj pad
local notation "cnt" => (L).bits spill
local notation "rank" => (L).nativeOrder enum
local notation "mass" => routeLoad (L).routes cnt

variable (sp : ∀i,Spine (rowGraph (B.datedLayout inj pad).edge) ((B.datedLayout inj pad).family i).1.1 ((B.datedLayout inj pad).routes i) ((B.datedLayout inj pad).family i).1.2)
    (pos : Fin N≃TurnShelf.Positions (B.datedLayout inj pad).routes) (col : Fin N→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin K×Fin slots)
    (widths : ∀i,col i 4=(B.datedLayout inj pad).bits spill (pos i).1)
    (site : ∀u : ProtocolRAMTurnShelf.Live col,(put u).1=(sp (pos u.val).1).visit (pos u.val).2)
    (before : _→Bool→ℕ) (after : Fin edges→Bool→ℕ)
    (role : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)=
      refRole (B.datedLayout inj pad).routes before after (pos u.val).1 (TurnShelf.refAt (B.datedLayout inj pad).family (B.datedLayout inj pad).edge (B.datedLayout inj pad).routes sp (pos u.val) b))
    (start : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)=
      datedStart (B.datedLayout inj pad).family (B.datedLayout inj pad).edge (B.datedLayout inj pad).routes ((B.datedLayout inj pad).bits spill) ((B.datedLayout inj pad).nativeOrder enum) (pos u.val).1 (TurnShelf.refAt (B.datedLayout inj pad).family (B.datedLayout inj pad).edge (B.datedLayout inj pad).routes sp (pos u.val) b))
    (s : Fin K) (x : State ((commodityGraph π place).chordWidths spill) s)
    (y : State (B.actual.chordWidths (routeLoad B.ordinary spill)) s)
local notation "input" => cast (congrArg (fun C=>State C s) (B.spill_input_width inj pad spill).symm) x
local notation "output" => cast (congrArg (fun C=>State C s) (B.spill_output_width inj pad spill).symm) y

open ReportSockets HistoryRoles HistoryRoles.Terminal RoleProgram
variable {V : Type} [Fintype V] {wr attempts deg width : ℕ} (vtx : Site h (2^wr) k)
local notation "Fib" => Fiber (attempts:=attempts) S vtx
local notation "active" => fun side : Bool=>cond side (B.actual.chordWidths (routeLoad B.ordinary spill))
  ((commodityGraph π place).chordWidths spill)
variable (rest : Bool→Widths K) (z : ∀b,State (rest b+(cond b (B.actual.chordWidths (routeLoad B.ordinary spill)) ((commodityGraph π place).chordWidths spill))) s)
    (parts : ∀b,PassiveWindow.Parts ((portGraph K).Port s) (Fin deg) width (fun port=>(rest b+(cond b (B.actual.chordWidths (routeLoad B.ordinary spill)) ((commodityGraph π place).chordWidths spill))) port.val.1))
    (size : ∀b port,(rest b+(cond b (B.actual.chordWidths (routeLoad B.ordinary spill)) ((commodityGraph π place).chordWidths spill))) port≤width)
    (roleRoom : ∀a:(Fiber (attempts:=attempts) S vtx),∀t,RoleProgram.labelled S t a.val<2^p) (seat : (Fiber (attempts:=attempts) S vtx)→Fin deg)
local notation "bank" b => Function.uncurry (ChordAperture.canonical (parts b) (fun port=>Nat.testBit (z b port).val))

include sp pos widths site role start size in
/-- For the two genuine gathered banks, a live source needs just its dated
local role receipt and signed owner. All compared Boolean values follow
from the recorded starts and the mixed-radix splitting law. -/
theorem pooled_onlySpill (base : ℕ) (mem : Memory W)
    (ctrl : ℕ×ℕ→V⊕Bool) (v : V→Bool)
    (written : ∀f : Fin 5,∀a : Fin K×Fin slots,mem (TurnShelf.addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
    (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W)
    (roleFit : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e)
    (header : ∀ t : Fin slots,∀c : TurnShelf.Control p e,let u:=TurnShelf.projection c
      Sum.elim v id (ctrl (TurnShelf.addr base s t u.1,u.2))=(mem (TurnShelf.addr base s t u.1)).val.testBit u.2)
    (atOld : ∀i (digit:Fin (cnt i)) b (loc : (rowGraph (L).family).vertex i b=s),
      ∃a : Fib,before i b=RoleProgram.labelled S false a.val ∧ (parts false).owner (seat a)=some (sourcePort (L).family cnt
        (v:=s) ⟨(⟨i,digit⟩,b),by cases b <;>exact loc⟩))
    (atNew : ∀i (u : Fin ((L).routes i).length) (digit : Fin (cnt i)) b
      (loc : (rowGraph (L).edge).vertex (((L).routes i).get u) b=s),
      ∃a : Fib,after (((L).routes i).get u) b=RoleProgram.labelled S true a.val ∧
        (parts true).owner (seat a)=some (sourcePort (L).edge mass
          (datedHopPort (L).edge (L).routes cnt rank i u digit b s loc))) :
    TypedWiring.value (TurnShelf.physical (F:=F) (r:=slots) base s
      (fun key=>Sum.map (fun a=>Sum.inl (Sum.inl a)) id (ctrl key))
      (spillAperture S vtx roleRoom seat (e:=e))) (Sum.elim (Sum.elim v (bank false)) (bank true))=
      B.onlySpill inj pad spill enum s (splitPortState (rest false) (active false) s (z false)).2
        (splitPortState (rest true) (active true) s (z true)).2 := by
  apply physical_onlySpill B inj pad spill enum sp pos col put widths site before after role start s
    _ _ base mem _ _ _ written fieldFit roleFit extent
  · intro t c
    have peel (u : V⊕Bool) : Sum.elim (Sum.elim (Sum.elim v (bank false)) (bank true)) id
        (Sum.map (fun a=>Sum.inl (Sum.inl a)) id u)=Sum.elim v id u := by cases u <;>rfl
    exact (peel _).trans (header t c)
  · intro i d b loc q code digit
    obtain ⟨a,roleId,owner⟩:=atOld i d b loc
    exact spillAperture_row S vtx roleRoom seat s rest active z (L).family cnt false
      (B.spill_input_width inj pad spill) ⟨(⟨i,d⟩,b),by cases b <;> exact loc⟩ parts a q v
      (code.trans roleId) owner (size false _) digit
  · intro i u d b loc q code digit
    obtain ⟨a,roleId,owner⟩:=atNew i u d b loc
    apply spillAperture_row S vtx roleRoom seat s rest active z (L).edge mass true
      (B.spill_output_width inj pad spill) (datedHopPort (L).edge (L).routes cnt rank i u d b s loc)
      parts a q v (code.trans roleId) owner (size true _)
    simpa only [datedHopPort_edge,datedHopPort_offset,←Nat.add_assoc] using digit


end Hierarchy.ProbeStage.CoreBoard.Mount
end

end OAI
