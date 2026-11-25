import OAI.Hierarchy.DescentDatedSignedParentValues
import OAI.Hierarchy.DescentOrdinaryMaterialRoute

namespace OAI
/-! The actual two signed numerals under an equal natural capacity and a named
world. Integer coordinates make the snapshot stable under reindexing the native arrays. -/
namespace Hierarchy.DescentDatedAddressBook.SignedDrawing
open DescentSixParty DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U]
  {d H prior degree Q O K L b groups k age : ℕ} {bits : Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ} {A:GroupStage W G price ε (Fin groups) U k}
  {native:W.graph.Edge↪ℕ} {R:Fin prior→Fin degree→Option (Fin prior)}
  {symm:∀u v j,R u j=some v→∃n,R v n=some u} {host:U↪Fin H} {pitch:ℕ}
  {space:Fused.capacity degree Q K L≤2^b}
  {before:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Option (Fused.Raw R Q K L b)}
  {parent:Fin (2^k)→Fin O→Fin prior→Fin groups→Option (ParentFilter.Source (breadth degree) Q K L)}
  {marks:Fin (2^k)→Fin (breadth degree*O)→Fin H→Fin groups→Cell 1}
variable (d₀:SignedDrawing A native R symm host pitch space before parent marks)
    (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S age)

variable (capacity : A.cap=L)

def digits (x : Fin (2^k)) (j : Fin (breadth degree*O)) (h : Fin H) (g : Fin groups) : ℕ×ℕ :=by
  subst L
  exact ((d₀.peer S ready x j h g).val,(d₀.serial S ready x j h g).val)

def numbered (x j h g : ℕ) : ℕ×ℕ :=
  if bx : x<2^k then if bj : j<breadth degree*O then if bh : h<H then if bg : g<groups then
    d₀.digits S ready capacity ⟨x,bx⟩ ⟨j,bj⟩ ⟨h,bh⟩ ⟨g,bg⟩ else (0,0) else (0,0) else (0,0) else (0,0)

theorem numbered_entry (x : Fin (2^k)) (j : Fin (breadth degree*O)) (h : Fin H) (g : Fin groups) :
    d₀.numbered S ready capacity x.val j.val h.val g.val=d₀.digits S ready capacity x j h g :=by
  simp only [numbered,dite_eq_left x.isLt,dite_eq_left j.isLt,dite_eq_left h.isLt,dite_eq_left g.isLt]

structure Slot where
  block : ℕ
  role : ℕ
  host : ℕ
  group : ℕ
  marked : Bool

/-- The exact numerical location of a live parent on the corresponding signed face. -/
def locate (e : d₀.edge) (side : Bool) : Option Slot :=by
  letI:=d₀.finiteEdge
  letI:=d₀.finiteRaw
  letI:=d₀.finiteTicket
  let h:=if side then d₀.blocks.dst e else d₀.blocks.src e
  exact if pos:0<d₀.blocks.count e then
    let ent : DescentParallelBase.Local d₀.blocks h:=⟨e,pos,by cases side <;> simp [h]⟩
    let j:=(Measured.roster d₀.blocks R symm d₀.observed).address h ent
    some ⟨h.2.val,j.val,(host h.1.2).val,h.1.1.val,decide (d₀.core e)⟩
  else none

local instance numberEdgeFintype : Fintype d₀.edge := d₀.finiteEdge
local instance numberRawFintype : Fintype d₀.raw := d₀.finiteRaw
local instance numberTicketFintype : Fintype d₀.ticket := d₀.finiteTicket

local notation "rr" => Measured.roster d₀.blocks R symm d₀.observed

theorem role_at_visit (h : Stage.Host (Fin groups) U k) (e : DescentParallelBase.Local d₀.blocks h)
    (p : Fin (breadth degree)) (visited : Gather.select (Gather.reaching R) (d₀.observed.venue h).1 p=
      some (d₀.observed.loc (d₀.observed.raw h e)).1) :
    ((rr).address h e)=finProdFinEquiv (p,(d₀.observed.loc (d₀.observed.raw h e)).2) :=by
  let:=d₀.finiteEdge
  let:=d₀.finiteRaw
  let:=d₀.finiteTicket
  let visit:=Measured.visit d₀.blocks R symm d₀.observed h e
  have actual : Gather.select (Gather.reaching R) (d₀.observed.venue h).1 visit=
      some (d₀.observed.loc (d₀.observed.raw h e)).1 :=
    Resident.visit_read d₀.blocks h (fun b=>(d₀.observed.venue b).1) d₀.observed.loc (d₀.observed.raw h)
      (Gather.reaching R) (Measured.near d₀.blocks R symm d₀.observed h) e
  have unique:=Gather.once (Gather.reaching R) (d₀.observed.venue h).1
    (d₀.observed.loc (d₀.observed.raw h e)).1 (Measured.near d₀.blocks R symm d₀.observed h e)
  exact congrArg (fun j=>finProdFinEquiv (j,(d₀.observed.loc (d₀.observed.raw h e)).2)) (unique.unique actual visited)

theorem receiver_on_tape (h : Stage.Host (Fin groups) U k) (positive : 0<pitch) :
    DescentRawCablePanel.DepotRAM.Material.Route.receiver prior pitch (host h.1.2)=some (d₀.observed.venue h).1 :=by
  have coord:=d₀.coordinate h
  have low:=d₀.low h
  have quotient : (host h.1.2).val/pitch=(d₀.observed.venue h).1.val :=by
    rw [coord,Nat.mul_comm _ pitch,Nat.mul_add_div positive,Nat.div_eq_of_lt low,Nat.add_zero]
  have inside : (host h.1.2).val/pitch<prior:=quotient.symm ▸ (d₀.observed.venue h).1.isLt
  simp only [DescentRawCablePanel.DepotRAM.Material.Route.receiver,dite_eq_left (And.intro positive inside)]
  exact congrArg some (Fin.ext quotient)

variable {W' : MarkedWorld F d Pin bits} (eqn : W=W') (chronology : DescentPacking.originalId W.graph.Edge=native)
local notation "A₁" => cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin groups) U k) eqn) A
variable (drawing : SignedDrawing (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin groups) U k) eqn) A) (DescentPacking.originalId W'.graph.Edge) R symm host pitch space before parent marks)
theorem named_numbers (ready' : (A₁).StateBounds S age) (capacity' : (A₁).cap=L) :
    (named A native R symm host pitch space before parent marks eqn chronology drawing).numbered S ready capacity=
      drawing.numbered S ready' capacity' :=by
  subst W'
  subst native
  rfl

end
end Hierarchy.DescentDatedAddressBook.SignedDrawing

end OAI
