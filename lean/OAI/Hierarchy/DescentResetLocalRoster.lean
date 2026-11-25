import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentParallelBase
import OAI.Hierarchy.DescentResetCableSlots

namespace OAI
/-! # Sparse disjoint slots for the actual positive parents at a receiver -/
namespace Hierarchy.DescentResetLocalRoster
open DescentParallelBase DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section

abbrev code (r : ℕ) := ↥(DescentHostDirectory.codes r)
abbrev Root (r Y : ℕ) := code r ⊕ (code r×Option (Fin Y))

def rootId (r Y : ℕ) : Root r Y↪Fin (rootSlots r Y) :=
  DescentResetCableSlots.sum (DescentResetCableSlots.interval r)
    (DescentResetCableSlots.prod (DescentResetCableSlots.interval r) DescentResetCableSlots.optional)

def localPrivateId (r Y K : ℕ) : (Bool×Root r Y×Fin K)↪Fin (2*(rootSlots r Y*K)) :=
  DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding
    (DescentResetCableSlots.prod (rootId r Y) (Function.Embedding.refl _))

theorem localPrivateId_val {r Y K : ℕ} (s : Bool) (q : Root r Y) (e : Fin K) :
    (localPrivateId r Y K (s,q,e)).val=
      (finTwoEquiv.symm s).val*(rootSlots r Y*K)+(rootId r Y q).val*K+e.val := by
  simp [localPrivateId,DescentResetCableSlots.prod,finProdFinEquiv,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]

variable {E U : Type} [Fintype E] [DecidableEq U] {n : ℕ} {board : Ends U n}
variable (C : Blocks board E) (u : U)

def active (e : E) := 0<C.count e ∧ (C.src e=u ∨ C.dst e=u)
abbrev Part {A : Type*} (wire : A→E) := {a : A // active C u (wire a)}

def split {A B : Type*} {K L : ℕ} (P : A⊕B→Prop)
    (left : {a // P (.inl a)}↪Fin K) (right : {b // P (.inr b)}↪Fin L) :
    {p // P p}↪Fin (K+L) :=
  let choose : {p // P p}↪({a // P (.inl a)}⊕{b // P (.inr b)}) :=
    { toFun := fun x=>match x with
        | ⟨.inl a,h⟩=>.inl ⟨a,h⟩
        | ⟨.inr b,h⟩=>.inr ⟨b,h⟩
      inj' := by
        rintro ⟨a|b,ha⟩ ⟨c|d,hc⟩ eqn
        · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val (Sum.inl.inj eqn)))
        · contradiction
        · contradiction
        · exact Subtype.ext (congrArg Sum.inr (congrArg Subtype.val (Sum.inr.inj eqn))) }
  choose.trans (DescentResetCableSlots.sum left right)

/-- The four disjoint constructors are signed original stems, hub trunks,
direct contacts, and a side/root-indexed sigma of rotor or tree cables. -/
def addresses {A B D F : Type*} (wire : E≃A⊕(B⊕(D⊕F))) {a b d f : ℕ}
    (stem : Part C u (fun x=>wire.symm (.inl x))↪Fin a)
    (trunk : Part C u (fun x=>wire.symm (.inr (.inl x)))↪Fin b)
    (contact : Part C u (fun x=>wire.symm (.inr (.inr (.inl x))))↪Fin d)
    (device : Part C u (fun x=>wire.symm (.inr (.inr (.inr x))))↪Fin f) :
    Local C u↪Fin (a+(b+(d+f))) :=
  let P:=fun p=>active C u (wire.symm p)
  let get : Local C u↪{p // P p}:=
    { toFun := fun e=>⟨wire e.val,by simpa [P,active,Local] using e.property⟩
      inj' := fun _ _ eqn=>Subtype.ext (wire.injective (congrArg Subtype.val eqn)) }
  get.trans (split P stem (split (fun q=>P (.inr q)) trunk
    (split (fun q=>P (.inr (.inr q))) contact device)))


section Numerals
variable {A B D F : Type*} (wire : E≃A⊕(B⊕(D⊕F))) {a b d f : ℕ}
  (stem : Part C u (fun x=>wire.symm (.inl x))↪Fin a)
  (trunk : Part C u (fun x=>wire.symm (.inr (.inl x)))↪Fin b)
  (contact : Part C u (fun x=>wire.symm (.inr (.inr (.inl x))))↪Fin d)
  (device : Part C u (fun x=>wire.symm (.inr (.inr (.inr x))))↪Fin f)
local notation "select" => addresses C u wire stem trunk contact device
local notation "parts" => split (fun z=>active C u (Equiv.symm wire z)) stem
  (split (fun z=>active C u (Equiv.symm wire (Sum.inr z))) trunk
    (split (fun z=>active C u (Equiv.symm wire (Sum.inr (Sum.inr z)))) contact device))

omit [Fintype E] [DecidableEq U] in
private theorem number_at (x : A⊕(B⊕(D⊕F))) (hx : active C u (wire.symm x)) :
    (select ⟨wire.symm x,hx⟩).val=(parts ⟨x,hx⟩).val := by
  let z : {p : A⊕(B⊕(D⊕F)) // active C u (wire.symm p)} :=
    ⟨wire (wire.symm x),by simpa using hx⟩
  change (parts z).val=_
  exact congrArg (fun y : {p : A⊕(B⊕(D⊕F)) // active C u (wire.symm p)} => (parts y).val)
    (show z=⟨x,hx⟩ from Subtype.ext (wire.apply_symm_apply x))

omit [Fintype E] [DecidableEq U] in
theorem stem_number (x : A) (hx : active C u (wire.symm (.inl x))) :
    (select ⟨wire.symm (.inl x),hx⟩).val=(stem ⟨x,hx⟩).val := by
  exact number_at C u wire stem trunk contact device (.inl x) hx

omit [Fintype E] [DecidableEq U] in
theorem trunk_number (x : B) (hx : active C u (wire.symm (.inr (.inl x)))) :
    (select ⟨wire.symm (.inr (.inl x)),hx⟩).val=a+(trunk ⟨x,hx⟩).val := by
  exact number_at C u wire stem trunk contact device (.inr (.inl x)) hx

omit [Fintype E] [DecidableEq U] in
theorem contact_number (x : D) (hx : active C u (wire.symm (.inr (.inr (.inl x))))) :
    (select ⟨wire.symm (.inr (.inr (.inl x))),hx⟩).val=a+b+(contact ⟨x,hx⟩).val := by
  rw [number_at C u wire stem trunk contact device]
  exact (Nat.add_assoc a b (contact ⟨x,hx⟩).val).symm

omit [Fintype E] [DecidableEq U] in
theorem device_number (x : F) (hx : active C u (wire.symm (.inr (.inr (.inr x))))) :
    (select ⟨wire.symm (.inr (.inr (.inr x))),hx⟩).val=a+b+d+(device ⟨x,hx⟩).val := by
  rw [number_at C u wire stem trunk contact device]
  change a+(b+(d+(device ⟨x,hx⟩).val))=a+b+d+(device ⟨x,hx⟩).val
  simp only [Nat.add_assoc]

end Numerals

/-- Semantic readback at a fixed slot. The field publisher supplies the same
option by reading the local descriptor at that address. -/
def origin {K : ℕ} (rank : Local C u↪Fin K) (j : Fin K) : Option (Local C u) :=
  if h : ∃e,rank e=j then some h.choose else none

theorem origin_iff {K : ℕ} (rank : Local C u↪Fin K) (j : Fin K) (e : Local C u) :
    origin C u rank j=some e ↔ rank e=j := by
  unfold origin
  split
  next hit =>
    constructor
    · intro found
      have eqn:=Option.some.inj found
      exact eqn ▸ hit.choose_spec
    · intro eqn
      exact congrArg some (rank.injective (hit.choose_spec.trans eqn.symm))
  next miss => simp only [reduceCtorEq,false_iff];exact fun eqn=>miss ⟨e,eqn⟩

theorem covers {K : ℕ} (rank : Local C u↪Fin K) (e : Local C u) :
    ∃! j : Fin K,origin C u rank j=some e :=
  ⟨rank e,(origin_iff C u rank _ _).mpr rfl,fun j h=>((origin_iff C u rank j e).mp h).symm⟩

theorem origin_sum {K : ℕ} (rank : Local C u↪Fin K) (f : Local C u→ℕ) :
    (∑j : Fin K,(origin C u rank j).elim 0 f)=∑e : Local C u,f e := by
  have read (e : Local C u) : origin C u rank (rank e)=some e:=(origin_iff C u rank _ _).mpr rfl
  symm
  apply Finset.sum_of_injOn rank
  · exact rank.injective.injOn
  · exact fun _ _=>Finset.mem_univ _
  · intro j _ outside
    cases h : origin C u rank j with
    | none=>rfl
    | some e=>exact False.elim (outside ⟨e,Finset.mem_univ _,(origin_iff C u rank j e).mp h⟩)
  · intro e _
    exact (congrArg (fun z : Option (Local C u) => z.elim 0 f) (read e)).symm


end
end Hierarchy.DescentResetLocalRoster

end OAI
