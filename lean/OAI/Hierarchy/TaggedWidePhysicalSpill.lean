import OAI.Hierarchy.TaggedWideSpillHopWords
import OAI.Hierarchy.TaggedWireTurnPhysical
import OAI.Hierarchy.TaggedWireTurnSparseMatrix
import OAI.Hierarchy.TaggedWireSpillMatrix

namespace OAI
/-! # The physical turn comparator for a dated spill -/

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

theorem spill_input_width : installedWidths (L).family cnt=(commodityGraph π place).chordWidths spill := by
  exact (L).installed spill

theorem spill_output_width : installedWidths (L).edge mass=B.actual.chordWidths (routeLoad B.ordinary spill) := by
  have tally : mass=routeLoad B.ordinary spill := by
    funext f
    exact (L).measured spill f
  rw [tally]
  exact filled_width _ pad _ (B.spill_off_loop inj spill)

omit [Field F] in
private theorem rebase_at {A B U V : Widths K} (left : A=B) (right : U=V)
    (M : SiteMatrix (State A) (State U) F) (s : Fin K) (x : State B s) (y : State V s) :
    (rebase left right M) s x y=M s (cast (congrArg (fun C=>State C s) left.symm) x)
      (cast (congrArg (fun C=>State C s) right.symm) y) := by subst B;subst V;rfl

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

include sp pos widths site role start in
/-- Both ends of an intermediate core edge read the actual local state at
this date. The selected outgoing bit is the preceding same-edge spill mass
plus its digit in the original commodity, even on a repeated edge. -/
theorem physical_onlySpill {V : Type} [Fintype V] (base : ℕ) (mem : Memory W)
    (control : ℕ×ℕ→V⊕Bool) (aperture : TurnShelf.Aperture p e→V⊕Bool) (assignment : V→Bool)
    (written : ∀f : Fin 5,∀a : Fin K×Fin slots,mem (TurnShelf.addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
    (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W)
    (roleFit : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e)
    (header : ∀ t : Fin slots,∀c : TurnShelf.Control p e,let u:=TurnShelf.projection c
      Sum.elim assignment id (control (TurnShelf.addr base s t u.1,u.2))=(mem (TurnShelf.addr base s t u.1)).val.testBit u.2)
    (prior : ∀i (j : Fin (cnt i)) b (loc : (rowGraph (L).family).vertex i b=s) (q : TurnShelf.Aperture p e),
      q.1.val=before i b→q.2.val=datedBase (L).family cnt i+j.val→Sum.elim assignment id (aperture q)=
        rowBits (L).family cnt input ⟨(⟨i,j⟩,b),by cases b <;>exact loc⟩)
    (next : ∀i (u : Fin ((L).routes i).length) (j : Fin (cnt i)) b
      (loc : (rowGraph (L).edge).vertex (((L).routes i).get u) b=s) (q : TurnShelf.Aperture p e),
      q.1.val=after (((L).routes i).get u) b→q.2.val=datedBase (L).edge mass (((L).routes i).get u)+NativeSlot.start (L).routes cnt rank i u+j.val→
        Sum.elim assignment id (aperture q)=
          rowBits (L).edge mass output (datedHopPort (L).edge (L).routes cnt rank i u j b s loc)) :
    TypedWiring.value (TurnShelf.physical (F:=F) (r:=slots) base s control aperture) assignment=
      B.onlySpill inj pad spill enum s x y := by
  rw [TurnShelf.physical_value base s control aperture assignment mem header]
  change _=rebase (B.spill_input_width inj pad spill) (B.spill_output_width inj pad spill)
    ((L).operator spill rank) s x y
  rw [rebase_at]
  apply TurnShelf.scattered_matrix (L).family (L).edge (L).routes cnt sp pos col put widths site F base mem rank
    (L).paths written fieldFit roleFit extent s input output (Sum.elim assignment id ∘ aperture)
  intro u localSite b j q code digit
  rw [role] at code
  rw [start] at digit
  have valid:=valid_pair (L).family (L).edge (L).routes (pos u.val).1 (sp (pos u.val).1) (pos u.val).2
  have whereAt:=(site u).symm.trans localSite
  rw [whereAt] at valid
  let ref:=TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b
  have ok : ValidRef (L).family (L).edge (L).routes (pos u.val).1 s ref := by
    cases b <;> first | exact valid.1 | exact valid.2
  change _=readTurn _ _ _ _ _ _ _ _ ref
  change q.1.val=refRole _ before after _ ref at code
  change q.2.val=datedStart _ _ _ cnt rank _ ref+j.val at digit
  cases choice : ref with
  | inl side =>
    rw [choice] at ok code digit
    exact (prior _ j side ok q code (by simpa [datedStart,refRole,refStart] using digit)).trans
      (turn_start_bit (L).family (L).edge (L).routes cnt rank _ j side s ok
        (rowBits (L).family cnt input) (rowBits (L).edge mass output)).symm
  | inr nextRef =>
    rcases nextRef with ⟨n,side⟩
    rw [choice] at ok code digit
    obtain ⟨within,atSite⟩:=ok
    let t : Fin ((L).routes (pos u.val).1).length:=⟨n,within⟩
    exact (next _ t j side atSite q (by simpa [refRole,within,t] using code)
      (by simpa [datedStart,refRole,refStart,within,t] using digit)).trans
      (datedTurn_bit (L).family (L).edge (L).routes cnt rank _ t j side s atSite
        (rowBits (L).family cnt input) (rowBits (L).edge mass output)).symm

end Hierarchy.ProbeStage.CoreBoard.Mount
end

end OAI
