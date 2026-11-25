import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentPackedMatchStreamRank
import OAI.Hierarchy.DescentOldOccurrenceReceipt

namespace OAI
/-! # The packed source and destination handles of every actual old marked edge -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "Dest" => target A native S ready names
local notation "Addr" => address A native S ready
abbrev Events (h : J×V) := Σ x : Fin (2^k),PackedCensus.Out W A.pos A.block h x

def seats (h : J×V) : Events A h↪Port (2^k) (2*A.cap) where
  toFun q:=(q.1,Addr (h,q.1) q.2)
  inj' := by
    rintro ⟨x,e⟩ ⟨y,f⟩ eqn
    have hxy : x=y:=congrArg Prod.fst eqn
    subst y;exact congrArg (Sigma.mk x) ((Addr (h,x)).injective (congrArg Prod.snd eqn))

abbrev Active (c : ScanColonies he A.stage) (side : Bool) := {e : (N).Edge // active N W.core home color c side e}

def event (c : ScanColonies he A.stage) (side : Bool) : Active A he c side↪Events A (addr c).1 where
  toFun e:=⟨A.block ((N).src e.val),⟨e.val,⟨by rw [←source_host A he ((N).src e.val),e.property.2.1],rfl⟩,e.property.1⟩⟩
  inj' := fun _ _ eqn=>Subtype.ext (congrArg (fun e=>e.2.val) eqn)

def handle (c : ScanColonies he A.stage) (side : Bool) := (event A he c side).trans (seats A native S ready (addr c).1)

private theorem seat_order (h : J×V) (q r : Events A h) (block : q.1=r.1) :
    (seats A native S ready h q).2<(seats A native S ready h r).2 ↔ native q.2.val<native r.2.val := by
  obtain ⟨x,e⟩:=q;obtain ⟨y,f⟩:=r;change x=y at block;subst y;exact source_order A native S ready (h,x) e f

private theorem seat_at_block (h : J × V) (x : Fin (2^k))
    (e : PackedCensus.Out W A.pos A.block h x) :
    (seats A native S ready h ⟨A.block (W.graph.src e.val),
      ⟨e.val,⟨e.property.1.1,rfl⟩,e.property.2⟩⟩).2 = Addr (h,x) e := by
  obtain ⟨edge, ⟨pos, block⟩, marked⟩ := e
  subst x
  rfl

variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
local notation "n" => binCount (2^k) A.degree

include rank coord named fit winner sorted route df in
omit named sorted rank in
theorem handle_mem (c : ScanColonies he A.stage) (side : Bool) (z : Port (2^k) (2*A.cap)) :
    z∈stream (panel (addr c).1) n (heap (addr c).2) side ↔ ∃e : Active A he c side,handle A native S ready he c side e=z := by
  let h:=(addr c).1;let key:=heap (addr c).2
  rw [stream_mem]
  constructor
  · rintro ⟨site,v,occupies,_⟩
    obtain ⟨u,grp,shade,b⟩:=(site_member (short := short) (a := a) A native S ready names win next he fit winner c side z.1).mp site
    obtain ⟨e,slot,_⟩:=(all_ports A native S ready names win next (h,z.1) z.2 v df).mp occupies
    have atH : A.pos u=h := by rw [←source_host A he u,grp]
    have eqn : (N).src e.val=u := coord (Prod.ext (e.property.1.1.trans atH.symm) (e.property.1.2.trans b.symm))
    let k : Active A he c side:=⟨e.val,e.property.2,by simpa only [eqn] using grp,by simpa only [eqn] using shade⟩
    exact ⟨k,Prod.ext e.property.1.2 ((seat_at_block A native S ready h z.1 e).trans slot)⟩
  · rintro ⟨e,rfl⟩
    let q:=event A he c side e
    exact ⟨(site_member (short := short) (a := a) A native S ready names win next he fit winner c side _).mpr ⟨_,e.property.2.1,e.property.2.2,rfl⟩,
      Dest (h,q.1) q.2,peer_at A native S ready names win next (h,q.1) q.2 df,
      subword A native S ready names win next he fit winner h q.1 q.2 route⟩

def originalA (side : Bool) (e : (N).Edge) := if side then PositiveAperture.rank (home ((N).dst e)) else originalId (N).Site ((N).src e)
def originalB (side : Bool) (e : (N).Edge) := if side then originalId (N).Site ((N).src e) else PositiveAperture.rank (home ((N).dst e))

private theorem tie {I : Type*} (f g : I→ℕ) (rel : ∀x y,f x<f y↔g x<g y) (x y) : f x=f y ↔ g x=g y := by
  have h:=rel x y;have k:=rel y x;omega

private theorem lex_side_iff {I : Type*} (side : Bool) (x j src dest leftTail rightTail : I → ℕ)
    (before : ∀ e f, x e < x f ↔ src e < src f)
    (dests : ∀ e f, j e < j f ↔ dest e < dest f) (e f : I)
    (wire : x e = x f → (leftTail e < leftTail f ↔ rightTail e < rightTail f)) :
    lex3 (fun z => if side then j z else x z) (fun z => if side then x z else j z) leftTail e f ↔
      lex3 (fun z => if side then dest z else src z) (fun z => if side then src z else dest z)
        rightTail e f := by
  have eqX := tie x src before e f
  have eqJ := tie j dest dests e f
  by_cases same : x e = x f
  · have tail := wire same
    cases side <;> simp only [lex3, Bool.false_eq_true, ite_true, ite_false,
      before e f, dests e f, eqX, eqJ, tail]
  · have diff : src e ≠ src f := fun h => same (eqX.mpr h)
    cases side <;> simp only [lex3, Bool.false_eq_true, ite_true, ite_false,
      before e f, dests e f, same, diff, eqJ, false_and, or_false]

include rank coord named fit winner sorted route df in
theorem handle_order (edgeOrder : ∀e f,native e<native f ↔ originalId (N).Edge e<originalId (N).Edge f)
    (c : ScanColonies he A.stage) (side : Bool) (e f : Active A he c side) :
    let u:=panel (addr c).1;let ptr:=handle A native S ready he c side
    lex3 (primary u side) (secondary u side) (fun z=>z.2.val) (ptr e) (ptr f) ↔
      lex3 (originalA A he side) (originalB A he side) (originalId (N).Edge) e.val f.val := by
  intro u ptr
  let h:=(addr c).1;let ev:=event A he c side
  let p:=places (short := short) (a := a) A native S ready names win next he rank coord named fit winner sorted h
  let get (z : Active A he c side):=Dest (h,(ev z).1) (ev z).2
  let src (z : Active A he c side):=originalId (N).Site ((N).src z.val)
  let dest (z : Active A he c side):=PositiveAperture.rank (home ((N).dst z.val))
  let x (z : Active A he c side):=(ptr z).1.val
  let j (z : Active A he c side):=targetCode u (ptr z)
  have place (z : Active A he c side) : A.pos ((N).src z.val)=h := (ev z).2.property.1.1
  have before (z b : Active A he c side) : x z<x b ↔ src z<src b := by
    have cmp := site_name_order A rank coord named ((N).src z.val) ((N).src b.val)
    rw [place z, place b, Nat.add_lt_add_iff_left] at cmp
    exact cmp.symm
  have port (z : Active A he c side) : peer u (ptr z).1 (ptr z).2=some (get z) := peer_at A native S ready names win next (h,_) (ev z).2 df
  have hit (z : Active A he c side) : p.actor (get z) (ptr z).1=some ((N).dst z.val) :=
    (actor_iff A next coord h _ _ _).mpr ⟨route _ _ (ev z).2,(A.same z.val).symm⟩
  have dests (z b : Active A he c side) : j z<j b ↔ dest z<dest b := by
    have code (v : Active A he c side) : j v = bin u (get v) (ptr v).1 := by
      simp only [j, targetCode, port v, Option.map_some, Option.getD_some]
    rw [code z, code b]
    exact (p.ordered (scanHomeAt_surjective he A.stage) (group_order A he) (hit z) (hit b)).symm
  have wire (eqn : x e=x f) : (ptr e).2.val<(ptr f).2.val ↔ originalId (N).Edge e.val<originalId (N).Edge f.val :=
    (seat_order A native S ready h (ev e) (ev f) (Fin.ext eqn)).trans (edgeOrder _ _)
  exact lex_side_iff side x j src dest (fun z => (ptr z).2.val)
    (fun z : Active A he c side => originalId (N).Edge z.val) before dests e f wire


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
