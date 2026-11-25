import OAI.Hierarchy.DescentCanonicalPorts
import OAI.Hierarchy.DescentObservedReservations

namespace OAI
/-! # Extend all occupied contacts to the block-independent good rotor port template -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile DescentCanonicalPorts DescentRouterSlots
open scoped BigOperators Classical
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {k m n g Δ K : ℕ}
variable (D : Dyadic V I k) (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
variable (localEdge : ∀i : D.Paid,(D.old true i.val).1∈near (D.old false i.val).1)
variable (same : ∀i : D.Paid,(D.old true i.val).2=(D.old false i.val).2)
variable (low : ∀v,m≤D.b v)
local notation "short" => DescentCanonicalPorts.short (m:=m) D.b
local notation "hi" => DescentCanonicalPorts.coarse (m:=m) D.b
local notation "rel" => DescentCanonicalPorts.relative (m:=m) D.b
local notation "Y" => (2^n:ℕ)

private theorem seen (a : D.Pairs) : ∃z:D.Paid,D.edge z=a := by
  rcases a with ⟨a,h⟩
  obtain ⟨z,_,ez⟩ := Finset.mem_image.mp h
  exact ⟨z,Subtype.ext ez⟩

include same low in
theorem edge_block (s : Bool) (a : D.Pairs) : hi (D.endAt (!s) a).val=hi (D.endAt s a).val := by
  obtain ⟨p,rfl⟩ := seen D a
  cases s <;> simp [edge,endAt,ordered,endpoint,DescentChosenRouter.base,base_div D.b low D.hk,same]

include same low in
theorem edge_roster (s : Bool) (a : D.Pairs) :
    (short (D.endAt (!s) a).val).2∈touching (rel (D.endAt s a).val.1) (rel (D.endAt (!s) a).val.1)
      (short (D.endAt s a).val).2 := by
  obtain ⟨p,rfl⟩ := seen D a
  have lift (left right : V × Block k) (shared : left.2 = right.2) :
      (short (baseOf D.b D.hk D.L right)).2 ∈ touching (rel left.1) (rel right.1)
        (short (baseOf D.b D.hk D.L left)).2 := by
    rcases left with ⟨v,x⟩
    rcases right with ⟨w,y⟩
    change x = y at shared
    subst y
    exact physical_touch D.b low D.hk D.L v w x
  cases s with
  | false => exact lift (D.old false p.val) (D.old true p.val) (same p).symm
  | true => exact lift (D.old true p.val) (D.old false p.val) (same p)

include sym localEdge in
theorem edge_near (s : Bool) (a : D.Pairs) : (D.endAt (!s) a).val.1∈near (D.endAt s a).val.1 := by
  obtain ⟨p,rfl⟩ := seen D a
  cases s
  · exact localEdge p
  · exact (sym _ _).mp (localEdge p)

def relativeContact (s : Bool) (p : D.G) : D.Incident s p ↪
    Potential (m:=m) near D.b p.val.1 (short p.val).2 where
  toFun i := ⟨⟨(D.endAt (!s) i.val).val.1,by simpa only [i.property] using edge_near D near sym localEdge s i.val⟩,
    ⟨(short (D.endAt (!s) i.val).val).2,by simpa only [i.property] using edge_roster D same low s i.val⟩⟩
  inj' a b eq := by
    have other : (D.endAt (!s) a.val).val=(D.endAt (!s) b.val).val := by
      apply recover (m:=m) D.b
      · rw [edge_block D same low s a.val,edge_block D same low s b.val,a.property,b.property]
      · exact Prod.ext (congrArg (fun z=>z.1.val) eq) (congrArg (fun z=>z.2.val) eq)
    have h : D.endAt (!s) a.val=D.endAt (!s) b.val := Subtype.ext other
    have t := a.property.trans b.property.symm
    apply Subtype.ext
    apply Subtype.ext
    cases s with
    | false => exact Prod.ext t h
    | true => exact Prod.ext h t

variable {B S unit : ℝ} (L : D.Loads (2^n) B S unit) (pos : 0<S) (pu : 0<unit)
variable (cap : V→V→ℝ) (amount : ∀a s,L.cap a=cap (D.endAt s a).val.1 (D.endAt (!s) a).val.1)
variable (nonneg : ∀v w,0≤cap v w)
variable (paid : ∀v id,(∑w∈near v,∑_j∈touching (D.b v) (D.b w) id,cap v w)≤2*S)
variable (smooth : ∀v w,w∈near v→D.b w≤D.b v+g) (degree : ∀v,(near v).card≤Δ)
variable (budget : Δ*2^g≤K) (space : 4*K≤2^n)
local notation "roster" => relativeContact D near sym localEdge same low
local notation "draw" => slots near D.b low cap S pos nonneg paid smooth degree budget space D.hostNumber

def channel (s : Bool) (p : D.G) :
    (Σa : D.Incident s p,Fin (D.span L a.val)) ↪ Socket (m:=m) («Y»:=Y) near D.b cap S p.val.1 (short p.val).2 where
  toFun i := ⟨roster s p i.1,i.2.cast (by
    change rowCount Y S (L.cap i.1.val)=rowCount Y S (cap p.val.1 (D.endAt (!s) i.1.val).val.1)
    rw [amount i.1.val s,i.1.property])⟩
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have labels : a = b := (roster s p).injective (congrArg Sigma.fst h)
    subst b
    apply congrArg (Sigma.mk a)
    exact Fin.ext (congrArg (fun z : Socket (m:=m) («Y»:=Y) near D.b cap S p.val.1 (short p.val).2=>z.2.val) h)

def canonicalOutput (s : Bool) (p : D.G) :
    (Σa : D.Incident s p,Fin (D.span L a.val)) ↪ Fin Y :=
  (channel D near sym localEdge same low L cap amount s p).trans (draw p.val.1 (short p.val).2)

theorem extend_output (s : Bool) (p : D.G) :
    ∃σ : Equiv.Perm (Fin Y),∀j : Σa : D.Incident s p,Fin (D.span L a.val),
      σ (outputSlot _ (D.room L pos pu s p) j)=
        canonicalOutput D near sym localEdge same low L pos cap amount nonneg paid smooth degree budget space s p j :=
  Equiv.Perm.exists_extending_pair _ _ (outputSlot_injective _ _) (Function.Embedding.injective _)

def socketName (s : Bool) (c : Reserve (D.span L)) : AllSockets (m:=m) («Y»:=Y) near D.b cap S :=
  ⟨short (D.endAt s c.1).val,channel D near sym localEdge same low L cap amount s (D.endAt s c.1)
    ⟨⟨c.1,rfl⟩,c.2⟩⟩

local notation "socket" => socketName D near sym localEdge same low L cap amount
local notation "rows" => rowName near D.b low cap S pos nonneg paid smooth degree budget space D.hostNumber

theorem socket_key (s : Bool) (c : Reserve (D.span L)) :
    wireName (m:=m) («Y»:=Y) near D.b cap S (socket s c)=
      (short (D.endAt s c.1).val,short (D.endAt (!s) c.1).val,c.2.val) := rfl

/-- The identity of the opposite host port is a function of the local host
port in both directions, across *all* surviving blocks, even if two blocks
supply wholly different sets of observed good cables. -/
theorem same_peer (s : Bool) (c d : Reserve (D.span L))
    (atPort : rows (socket s c)=rows (socket s d)) :
    rows (socket (!s) c)=rows (socket (!s) d) := by
  have key := congrArg (wireName (m:=m) («Y»:=Y) near D.b cap S) ((rows).injective atPort)
  rw [socket_key,socket_key] at key
  apply congrArg rows
  apply (wireName (m:=m) («Y»:=Y) near D.b cap S).injective
  rw [socket_key,socket_key,Bool.not_not]
  exact congrArg (fun z : (V × ℕ) × (V × ℕ) × ℕ => (z.2.1, z.1, z.2.2)) key

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
