import OAI.Hierarchy.TaggedWidePassiveRows
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # Canonical contiguous chord words in immutable per-neighbor site apertures -/

noncomputable section
namespace Hierarchy.Tagged.ChordAperture
open ThreeFlat Routing
open PassiveWindow
open scoped BigOperators Classical

variable {F V P I : Type} [Field F] [Fintype V] [Fintype I] {W : ℕ} {t : P→ℕ}
variable (o : Parts P I W t) (fits : ∀p,t p ≤ W)

def code (i q : I) := ∃p,o.owner i=some p ∧ o.owner q=some p

def sizeAt (i q : I) : Fin (W+1) := if code o i q then ⟨o.width i,Nat.lt_succ_of_le (o.within i)⟩ else 0

def head (i : I) (side : Bool) : Fin (W+1) := if side then ⟨min W (o.base i),Nat.lt_succ_of_le (Nat.min_le_left ..)⟩ else 0

def room (q : I) : ℕ := (o.owner q).elim 0 t

def canonical (state : P→ℕ → Bool) (q : I) (j : Fin W) : Bool := (o.owner q).elim false
  (fun p=>if j.val<t p then state p j.val else false)

def padded (words : I → Bits W) := ∀q (j : Fin W),room o q ≤ j.val → words q j=false

def agrees (data words : I → Bits W) (i q : I) :=
  ∀p,o.owner i=some p → o.owner q=some p→∀u : Fin (o.width i),
    ∀j : Fin W,j.val=o.base i+u.val → data i (u.castLE (o.within i))=words q j

omit [Fintype I] in
theorem unique (state : P→ℕ → Bool) (data words : I → Bits W)
    (prior : ∀i p,o.owner i=some p→∀u : Fin (o.width i),data i (u.castLE (o.within i))=state p (o.base i+u.val)) :
    padded o words ∧ (∀i q,agrees o data words i q) ↔ words=canonical o state := by
  constructor
  · rintro ⟨pad,read⟩
    funext q j
    cases atq : o.owner q with
    | none=>simpa [canonical,atq] using pad q j (by simp [room,atq])
    | some p=>
      by_cases small : j.val<t p
      · obtain ⟨i,atI,u,eqn⟩ := o.covers p ⟨j.val,small⟩
        rw [canonical,atq,Option.elim_some,ite_eq_left small,←read i q p atI atq u j eqn.symm,prior i p atI,eqn]
      · simpa [canonical,atq,small] using pad q j (by simpa [room,atq] using Nat.le_of_not_gt small)
  · rintro rfl
    constructor
    · intro q j high
      cases e : o.owner q <;> simp_all [room,canonical]
    · intro i q p atI atq u j same
      have low : j.val<t p := same ▸ (Nat.add_lt_add_left u.isLt _).trans_le (o.top i p atI)
      rw [prior i p atI,canonical,atq,Option.elim_some,ite_eq_left low,same]

local notation "Pin" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits W) (BinaryBarrelTurns.digits W) W

def pairsNet (read : I×I → Pin → V⊕Bool) : BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (F:=F) (I:=I×I) (V:=V) (A:=fun _=>Pin) (fun _=>BinaryBarrelTurns.fixed F W) read

include fits in
omit [Fintype I] in
theorem pair_value (data words : I → Bits W) (i q : I) :
    TypedWiring.value (BinaryBarrelTurns.fixed F W)
      (BinaryBarrelTurns.pins ((addressEquiv _).symm (BinaryBarrelTurns.address (sizeAt o i q)))
        (fun s=>(addressEquiv _).symm (BinaryBarrelTurns.address (head o i s))) (PassiveWindow.data (data i) (words q)))=
      if agrees o data words i q then 1 else 0 := by
  rw [BinaryBarrelTurns.fixed_value]
  by_cases same : code o i q
  · obtain ⟨p,atI,atQ⟩ := same
    have somep : code o i q := ⟨p,atI,atQ⟩
    have endFit := (o.top i p atI).trans (fits p)
    have startFit : o.base i ≤ W := (Nat.le_add_right ..).trans endFit
    apply ite_congr ?_ (fun _=>rfl) (fun _=>rfl)
    apply propext
    constructor
    · intro eqn p' h1 h2 u j hj
      have check :=  eqn (u.castLE (o.within i)) (by simp [sizeAt,somep])
      have raw : u.val+o.base i<W := by omega
      have live : u.val<W := u.isLt.trans_le (o.within i)
      have target : (⟨u.val+o.base i,raw⟩ : Fin W)=j := by
        apply Fin.ext
        change u.val+o.base i=j.val
        exact (Nat.add_comm ..).trans hj.symm
      have index : u.castLE (o.within i)=(⟨u.val,live⟩ : Fin W) := Fin.ext rfl
      rw [index]
      simpa [head,PassiveWindow.data,Barrel.shift,Nat.min_eq_right startFit,raw,live,target] using check
    · intro eqn u used
      have small : u.val<o.width i := by simpa [sizeAt,somep] using used
      have loc : u.val+o.base i<W := by omega
      have read := eqn p atI atQ ⟨u.val,small⟩ ⟨_,loc⟩ (Nat.add_comm ..)
      simpa [head,PassiveWindow.data,Barrel.shift,Nat.min_eq_right startFit,loc] using read
  · have free : agrees o data words i q := by intro p l r;exact (same ⟨p,l,r⟩).elim
    simp [sizeAt,same,free]

include fits in
theorem eval (read : I×I → Pin → V⊕Bool) (v : V → Bool) (data words : I → Bits W)
    (pins : ∀i q,(Sum.elim v id)∘read (i,q)=
      BinaryBarrelTurns.pins ((addressEquiv _).symm (BinaryBarrelTurns.address (sizeAt o i q)))
        (fun s=>(addressEquiv _).symm (BinaryBarrelTurns.address (head o i s))) (PassiveWindow.data (data i) (words q))) :
    TypedWiring.value (pairsNet (F:=F) read) v=if ∀i q,agrees o data words i q then 1 else 0 := by
  rw [pairsNet,WideHost.localFamily_eval]
  have each (a : I×I) : TypedWiring.value (BinaryBarrelTurns.fixed F W) ((Sum.elim v id)∘read a)=if agrees o data words a.1 a.2 then 1 else 0 := by
    rcases a with ⟨i,q⟩
    rw [pins,pair_value o fits]
  simp_rw [each]
  rw [Fintype.prod_boole]
  simp only [Prod.forall]

end Hierarchy.Tagged.ChordAperture

end
end OAI
