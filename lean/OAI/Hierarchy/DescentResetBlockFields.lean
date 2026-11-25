import OAI.Hierarchy.DescentTrunkBundleMaps

namespace OAI
/-! # Read an installed reset block by its first physical bit and its address within that wire -/

namespace Hierarchy.DescentResetPointerFields
open DescentBundleHistory DescentKernelHistory DescentResetAttachments DescentNamedContact DescentRouterBank DescentOrderedWords
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {p : ℕ} (hp : 0<p) {A B : Type} {w : A→ℕ} {v : B→ℕ}
variable (route : BitRef w→BitRef v) (map : BlockMap p w v route)

/-- Both data fields are projections of an actual transported bit. The proof that a
complete p-bit payload fits relies only on correctness of the aligned map. -/
def firstBlock (b : BlockRef p w) : BlockRef p v where
  port := (route (b.atBit ⟨0,hp⟩)).1
  block := (route (b.atBit ⟨0,hp⟩)).2.val/p
  fits := by
    rw [←map.read b ⟨0,hp⟩]
    simpa [BlockRef.atBit,hp] using (map.map b).fits

private theorem block_ext (x y : BlockRef p v) (port : x.port=y.port) (row : x.block=y.block) : x=y := by
  cases x
  cases y
  cases port
  cases row
  rfl

theorem firstBlock_eq (b : BlockRef p w) : firstBlock hp route map b=map.map b := by
  apply block_ext
  · exact congrArg Sigma.fst (map.read b ⟨0,hp⟩).symm
  · change (route (b.atBit ⟨0,hp⟩)).2.val/p=(map.map b).block
    rw [←map.read]
    simp [BlockRef.atBit,hp]

theorem firstBlock_read (b : BlockRef p w) (d : Fin p) :
    (firstBlock hp route map b).atBit d=route (b.atBit d) := by rw [firstBlock_eq,map.read]

variable {n k L : ℕ} {P H Q : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network k (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e)
local notation "M" => DescentResetTrunks.network N home group R

def oldField (a : N.Site) (b : BlockRef p (boundaryWidth N a)) :=
  firstBlock hp (trunkOldBit N home group R key a) (oldBlockMap N home group R key whole a) b

def bankField (a : R.Site) (b : BlockRef p (boundaryWidth R a)) :=
  firstBlock hp (trunkBankBit N home group R key a) (bankBlockMap N home group R key whole hp a) b

omit [Fintype Q] in
theorem old_read (a : N.Site) (b : BlockRef p (boundaryWidth N a)) (d : Fin p) :
    (oldField hp N home group R key whole a b).atBit d=trunkOldBit N home group R key a (b.atBit d) :=
  firstBlock_read hp _ (oldBlockMap N home group R key whole a) b d

omit [Fintype Q] in
theorem bank_read (a : R.Site) (b : BlockRef p (boundaryWidth R a)) (d : Fin p) :
    (bankField hp N home group R key whole a b).atBit d=trunkBankBit N home group R key a (b.atBit d) :=
  firstBlock_read hp _ (bankBlockMap N home group R key whole hp a) b d

omit [Fintype Q] in
theorem old_at_source (a : N.Site) (e : Incident N a) (src : N.src e.val=a) (b : ℕ) (ok : (b+1)*p≤N.width e.val) :
    let f:=oldField hp N home group R key whole a ⟨.inl e,b,ok⟩
    (Sum.map Subtype.val Subtype.val f.port,f.block)=(Sum.inl (Sum.inl (false,e.val)),b) := by
  let fields := fun t : BitRef (boundaryWidth (M) (.inl (false,home a))) =>
    (Sum.map Subtype.val Subtype.val t.1,t.2.val/p)
  let input : BlockRef p (boundaryWidth N a) := ⟨.inl e,b,ok⟩
  change fields (trunkOldBit N home group R key a (input.atBit ⟨0,hp⟩)) = _
  simp only [input, BlockRef.atBit, trunkOldBit, dite_eq_left src]
  simp [fields, hp]

omit [Fintype Q] in
theorem old_at_pin (a : N.Site) (q : Attached N a) (b : ℕ) (ok : (b+1)*p≤bits q.val) :
    let f:=oldField hp N home group R key whole a ⟨.inr q,b,ok⟩
    (Sum.map Subtype.val Subtype.val f.port,f.block)=(Sum.inr q.val,b) := by
  simp [oldField,firstBlock,trunkOldBit,BlockRef.atBit,hp]

omit [Fintype Q] in
theorem old_at_target (a : N.Site) (e : Incident N a) (src : N.src e.val≠a)
    (b : ℕ) (ok : (b+1)*p≤N.width e.val) :
    let f:=oldField hp N home group R key whole a ⟨.inl e,b,ok⟩
    let dest:=DescentResetTrunks.moved N home
    let ow:=fun i : Fibre dest (home a)=>N.width i.val
    let item : Fibre dest (home a):=⟨e.val,congrArg home (e.property.resolve_left src)⟩
    (Sum.map Subtype.val Subtype.val f.port,f.block)=
      (Sum.inl (Sum.inr (Sum.inl (home a))),offset (DescentOrderedReset.fibreKey key dest (home a)) ow item/p+b) := by
  let fields := fun t : BitRef (boundaryWidth (M) (.inl (false,home a))) =>
    (Sum.map Subtype.val Subtype.val t.1,t.2.val/p)
  let input : BlockRef p (boundaryWidth N a) := ⟨.inl e,b,ok⟩
  change fields (trunkOldBit N home group R key a (input.atBit ⟨0,hp⟩)) = _
  simp only [input, BlockRef.atBit, trunkOldBit, dite_eq_right src]
  simp [fields]
  exact Nat.add_mul_div_right _ b hp

omit [Fintype Q] in
theorem bank_at_wire (a : R.Site) (e : Incident R a) (b : ℕ) (ok : (b+1)*p≤R.width e.val) :
    let f:=bankField hp N home group R key whole a ⟨.inl e,b,ok⟩
    (Sum.map Subtype.val Subtype.val f.port,f.block)=(Sum.inl (Sum.inr (Sum.inr e.val)),b) := by
  simp [bankField,firstBlock,trunkBankBit,BlockRef.atBit,hp]

omit [Fintype Q] in
/-- The first bit selects exactly one old edge interval in the sorted join socket. -/
theorem bank_at_pin (a : R.Site) (q : Attached R a) (b : ℕ)
    (ok : (b+1)*p≤publicWidth group N.width q.val) :
    let f:=bankField hp N home group R key whole a ⟨.inr q,b,ok⟩
    let k:=DescentOrderedReset.fibreKey key (group q.val.1) q.val.2
    let ow:=fun e : Fibre (group q.val.1) q.val.2=>N.width e.val
    let z : BlockRef p (boundaryWidth R a):=⟨.inr q,b,ok⟩
    let t:=(address k ow).symm (z.atBit ⟨0,hp⟩).2
    (Sum.map Subtype.val Subtype.val f.port,f.block)=
      (Sum.inl (Sum.inl (q.val.1,t.1.val)),t.2.val/p) := rfl

end
end Hierarchy.DescentResetPointerFields
namespace Hierarchy.DescentResetPointerFields
end Hierarchy.DescentResetPointerFields

end OAI
