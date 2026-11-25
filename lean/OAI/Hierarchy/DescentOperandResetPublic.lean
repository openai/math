import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentResetTerminalNodeFields

namespace OAI
/-! # Public operands of the retained and newly installed reset calls -/
namespace Hierarchy.DescentOperandStateBanks.Reset
open DescentKernelHistory DescentBundleHistory DescentNamedContact DescentRouterBank DescentResetTrunks Computability.BorderVNP.Crossing
open DescentResetPointerFields DescentOrderedWords DescentLaneGates
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {n d L p : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}

/-- Read the two parallel cable fields at this particular endpoint and copy
the original exterior ticket at an attached public port. -/
def boundaryName {E : Type} (cable : E→ℕ×ℕ) (ticket : P→ℕ) :
    (E⊕P)×ℕ → Pointer
  | (.inl e,g) => .cable (cable e).1 (cable e).2 g
  | (.inr v,g) => .pin (ticket v) g

def blockName {N : Network n P bits} {a : N.Site} (cable : N.Edge→ℕ×ℕ) (ticket : P→ℕ)
    (b : BlockRef p (boundaryWidth N a)) : Pointer :=
  boundaryName cable ticket (Sum.map Subtype.val Subtype.val b.port,b.block)

variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (hp : 0<p)
local notation "M" => DescentResetTrunks.network N home group R
variable (names : ((Bool × N.Edge) ⊕ (H ⊕ R.Edge)) → ℕ × ℕ) (ticket : P→ℕ)

omit [Fintype Q] in
/-- Reset moves an exterior port onto its new host. Both its original pin and
its aligned chunk are carried through the actual retained operand wire. -/
theorem exterior_source (a : N.Site) (port : Attached N a) (g : ℕ) (bound : (g+1)*p≤bits port.val) :
    blockName (N:=M) (a:=.inl (false,home a)) names ticket (oldField hp N home group R key whole a ⟨.inr port,g,bound⟩) =
      .pin (ticket port.val) g := by
  unfold blockName
  rw [old_at_pin]
  rfl

omit [Fintype Q] in
theorem first_wire (a : N.Site) (e : Incident N a) (atSource : N.src e.val=a)
    (g : ℕ) (bound : (g+1)*p≤N.width e.val) :
    let pair:=names (.inl (false,e.val))
    blockName (N:=M) (a:=.inl (false,home a)) names ticket (oldField hp N home group R key whole a ⟨.inl e,g,bound⟩)=
      .cable pair.1 pair.2 g := by
  intro pair
  unfold blockName
  rw [old_at_source hp N home group R key whole a e atSource g bound]
  rfl

omit [Fintype Q] in
theorem last_wire (a : N.Site) (e : Incident N a) (atTarget : N.src e.val≠a)
    (g : ℕ) (bound : (g+1)*p≤N.width e.val) :
    let w:=fun i : Fibre (moved N home) (home a)=>N.width i.val
    let item : Fibre (moved N home) (home a):=⟨e.val,congrArg home (e.property.resolve_left atTarget)⟩
    let first:=offset (DescentOrderedReset.fibreKey key (moved N home) (home a)) w item/p
    let pair:=names (.inr (.inl (home a)))
    blockName (N:=M) (a:=.inl (false,home a)) names ticket (oldField hp N home group R key whole a ⟨.inl e,g,bound⟩)=
      .cable pair.1 pair.2 (first+g) := by
  intro widths item first pair
  unfold blockName
  rw [old_at_target hp N home group R key whole a e atTarget g bound]
  rfl

omit [Fintype Q] in
theorem added_wire (a : R.Site) (e : Incident R a) (g : ℕ) (bound : (g+1)*p≤R.width e.val) :
    let pair:=names (.inr (.inr e.val))
    blockName (N:=M) (a:=.inr a) names ticket (bankField hp N home group R key whole a ⟨.inl e,g,bound⟩)=
      .cable pair.1 pair.2 g := by
  intro pair
  unfold blockName
  rw [bank_at_wire]
  rfl

omit [Fintype Q] in
theorem socket_wire (a : R.Site) (q : Attached R a) (g : ℕ) (bound : (g+1)*p≤publicWidth group N.width q.val) :
    let k:=DescentOrderedReset.fibreKey key (group q.val.1) q.val.2
    let ow:=fun e : Fibre (group q.val.1) q.val.2=>N.width e.val
    let z : BlockRef p (boundaryWidth R a):=⟨.inr q,g,bound⟩
    let t:=(DescentOrderedWords.address k ow).symm (z.atBit ⟨0,hp⟩).2
    let pair:=names (.inl (q.val.1,t.1.val))
    blockName (N:=M) (a:=.inr a) names ticket (bankField hp N home group R key whole a z)=
      .cable pair.1 pair.2 (t.2.val/p) := by
  intro k ow z t pair
  unfold blockName
  rw [bank_at_pin]
  rfl

variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)
    (src : ∀v,Shape p (old v)) (dev : ∀v,Shape p (bank v))
local notation "shape" => trunkShape N home group R key whole hp old bank src dev

omit [Fintype Q] in
/-- The actual retained recipe at the new address contains the very same
original copy ticket, even if a second copy of its slab is received there. -/
theorem retained_exterior (v : N.Site) (u : (old v).Node) (j : Fin (((src v).recipe hp).arity u))
    (a : Attached N v) (g : ℕ) (bound : (g+1)*p≤bits a.val)
    (was : ((src v).recipe hp).operand u j=.inl ⟨.inr a,g,bound⟩) :
    let now:=(shape (.inl (false,home v))).recipe hp
    let i:=Fin.cast (retained_terminal_arity N home group R key whole hp old bank src dev v u).symm j
    ∃b,now.operand ⟨⟨v,rfl⟩,u⟩ i=.inl b ∧ blockName (N:=M) (a:=.inl (false,home v)) names ticket b=.pin (ticket a.val) g := by
  intro now i
  let before : BlockRef p (boundaryWidth N v):=⟨.inr a,g,bound⟩
  refine ⟨(oldBlockMap N home group R key whole v).map before,
    retained_public N home group R key whole hp old bank src dev v u j before was,?_⟩
  have same : oldField hp N home group R key whole v before=(oldBlockMap N home group R key whole v).map before :=
    firstBlock_eq hp _ _ before
  rw [←same]
  exact exterior_source N home group R key whole hp names ticket v a g bound

end
end Hierarchy.DescentOperandStateBanks.Reset

end OAI
