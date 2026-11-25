import OAI.Computability.BorderVNP.CubePhysicalDeclaredPaths
import OAI.Computability.BorderVNP.CubeScatterLayout
import OAI.Computability.BorderVNP.CubeScatterSingletonRun

/-! # Assigning each physical packet bit to exactly one common list or private owner

Shared positions are indexed by the unordered pair of coordinate symbols, including
when both symbols have the same team owner. Local positions are indexed by the
owning team, retaining the complete physical identity of each bit within that team.
Unused slots of the rectangular packet banks have no bit index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.Assignment

open Crossing Physical VPVNP.MotifBase
open scoped Classical

variable {n d blocks b h K s D : ℕ} {Team : Type*}

/-- One actual payload bit after fixing the selector tuple. Supply lanes use the
selector-dependent width, so unoccupied slots of the physical bank add no choices. -/
abbrev BitIndex (b s : ℕ) (u : Packet n d blocks → Selector n K h) :=
  SingleSlot n d blocks (h*b) ⊕ (Packet n d blocks × Ends n × Fin (h*b)) ⊕
    (Σ p : Packet n d blocks, Σ e : Edge (n+1), Fin (payload (onEdge s) (u p).2 e))

/-- A shared unordered symbol row or an executing private team. -/
abbrev Region (d : ℕ) (Team : Type*) := Sym2 (Fin d) ⊕ Team

/-- Select the abstract vertex at the appropriate end of an antipodal demand wire. -/
def endVertex (e : Ends n) : Vertex (n+1) := if e.2 then stop e.1 else start e.1

/-- Each bit has one routing destination. A crossing supply or singleton uses one common
list even if both endpoint groups belong to the same team. -/
def route {u : Packet n d blocks → Selector n K h} (i : Fin (n+1)) (owner : Fin d → Team) :
    BitIndex b s u → Region d Team
  | .inl z => if z.1.val.1 i = z.1.val.2 i then .inr (owner (z.1.val.1 i))
    else .inl (itemRow i (.inr z))
  | .inr (.inl (p,e,_)) => .inr (owner (vertexLabel p (endVertex e) i))
  | .inr (.inr ⟨p,e,_⟩) => if e.2 = i then .inl (itemRow i (.inl p : Item n d blocks (h*b)))
    else .inr (owner (vertexLabel p e.1 i))

/-- Payload supplied by each common row and private owner, with its exact finite physical indices. -/
abbrev Choices (b s : ℕ) (u : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (owner : Fin d → Team) :=
  (r : Region d Team) → {k : BitIndex b s u // route i owner k = r} → Bool

/-- The payload lookup always uses the unique owner of this physical bit. -/
def lookup {u : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {owner : Fin d → Team}
    (choices : Choices b s u i owner) (k : BitIndex b s u) : Bool :=
  choices (route i owner k) ⟨k,rfl⟩

/-- Distribute and recombine the finite bits without duplicating an assignment, also
when distinct group symbols or different packets have the same owner. -/
def bitEquiv (u : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (owner : Fin d → Team) :
    (BitIndex b s u → Bool) ≃ Choices b s u i owner where
  toFun f _ k := f k.val
  invFun := lookup
  left_inv _ := rfl
  right_inv f := by
    funext r ⟨k,hk⟩
    subst r
    rfl

/-- At a fixed selector tuple, flatten the singleton, demand and supply assignments
of a physical path into the disjoint sum of their true indices. -/
def payloadEquiv (u : Packet n d blocks → Selector n K h) :
    ((SingleSlot n d blocks (h*b) → Bool) × (Packet n d blocks → Ports (fun _ : Ends n => h*b)) ×
      (∀ p, (packetNetwork D b s (u p)).Assignment)) ≃ (BitIndex b s u → Bool) where
  toFun bits k := match k with
    | .inl z => bits.1 z
    | .inr (.inl (p,e,j)) => bits.2.1 p e j
    | .inr (.inr ⟨p,e,j⟩) => bits.2.2 p e j
  invFun f := (fun z => f (.inl z),fun p e j => f (.inr (.inl (p,e,j))),fun p e j => f (.inr (.inr ⟨p,e,j⟩)))
  left_inv _ := rfl
  right_inv f := by
    funext k
    rcases k with z | (⟨p,e,j⟩|⟨p,e,j⟩) <;> rfl

variable {P : Type*} {bits : P → ℕ} {Cell : Type} [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)

/-- The same choices as an entire physical path, with one selector per packet and one
payload bit at its routed common list or private team. The chosen coordinate depends
on the selectors, and the internal cell assignments are carried through unchanged. -/
abbrev DistributedPath (n d blocks b h K s : ℕ) (owner : Fin d → Team) :=
  (∀ c, N.InsideAssignment cell c) ×
    ((u : Packet n d blocks → Selector n K h) × Choices b s u (chosen b s u) owner)

/-- The same physical choices when the declaration and greedy group owners are
recomputed separately for each selector tuple. -/
abbrev AdaptiveDistributedPath (n d blocks b h K s : ℕ)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team) :=
  (∀ c, N.InsideAssignment cell c) ×
    ((u : Packet n d blocks → Selector n K h) × Choices b s u (chosen b s u) (owners u))

/-- Bijection used in the global sum over passing computations. There is one choice of
all routed and local payloads for each selector tuple and physical path, and conversely. -/
def adaptivePathEquiv (n d blocks b h K s : ℕ)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team) :
    Path N cell n d blocks b h K s ≃ AdaptiveDistributedPath N cell n d blocks b h K s owners where
  toFun a :=
    let u := a.2.2.2.1
    let f := (payloadEquiv (D := D) (b := b) (s := s) u) (a.2.1,a.2.2.1,a.2.2.2.2)
    (a.1,⟨u,bitEquiv u (chosen b s u) (owners u) f⟩)
  invFun a :=
    let u := a.2.1
    let z := (payloadEquiv (D := D) u).symm (lookup a.2.2)
    (a.1,z.1,z.2.1,⟨u,z.2.2⟩)
  left_inv a := rfl
  right_inv a := by
    rcases a with ⟨inside,u,bits⟩
    let W := payloadEquiv (D := D) (b := b) (s := s) u
    let R := bitEquiv (b := b) (s := s) u (chosen b s u) (owners u)
    change ((inside,⟨u,R (W (W.symm (R.symm bits)))⟩) : AdaptiveDistributedPath N cell n d blocks b h K s owners) = _
    rw [W.apply_symm_apply,R.apply_symm_apply]

/-- Specialization to a fixed grouping of symbols into physical teams. -/
def pathEquiv (n d blocks b h K s : ℕ) (owner : Fin d → Team) :
    Path N cell n d blocks b h K s ≃ DistributedPath N cell n d blocks b h K s owner :=
  adaptivePathEquiv N cell n d blocks b h K s (fun _ => owner)

end Cube.Scatter.Assignment

end BorderVNP
end Computability
end OAI
