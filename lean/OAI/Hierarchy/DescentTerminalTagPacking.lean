import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.Routing.SwitchPad
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Independent tagged calls inside disjoint row blocks -/

namespace Hierarchy.Tagged.TerminalPack
open Computability.VPVNP.RAMSerialization
open ThreeFlat.Routing (widenRecord widenRecord_injective)
open scoped Classical BigOperators

/-- The high address bits name the block, and the low bits name its local row. -/
def rowPair (n s : ℕ) : Row (n+s) ≃ Row s × Row n where
  toFun r := ((wordBits s).symm (fun j => wordBits (n+s) r (Fin.natAdd n j)),
    (wordBits n).symm (fun j => wordBits (n+s) r (j.castAdd s)))
  invFun p := (wordBits (n+s)).symm (Fin.addCases (wordBits n p.2) (wordBits s p.1))
  left_inv r := by
    apply (wordBits (n+s)).injective
    rw [Equiv.apply_symm_apply]
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  right_inv p := by
    rcases p with ⟨a,i⟩
    simp

private noncomputable def pad {w h : ℕ} (hw : w ≤ h) : Bits w ↪ Bits h :=
  ⟨widenRecord h,widenRecord_injective hw⟩

private def payload {n s w : ℕ} (toPort : Row n × Fin w → Port n w)
    (r : Row (n+s)) (j : Fin (n+s)) : (Row s × Fin (pins n w)) ⊕ Bool :=
  if v : j.val < w then
    .inl ((rowPair n s r).1,portIndex n w (toPort ((rowPair n s r).2,⟨j.val,v⟩)))
  else .inr false

private def select (n s w : ℕ) : Port (n+s) (n+s) → (Row s × Fin (pins n w)) ⊕ Bool
  | .inl (r,j) => payload Sum.inl r j
  | .inr (.inr (r,j)) => payload (fun p => .inr (.inr p)) r j
  | .inr (.inl (r,j)) => Fin.addCases
      (fun low => .inl ((rowPair n s r).1,portIndex n w (.inr (.inl ((rowPair n s r).2,low)))))
      (fun high => .inr (wordBits s (rowPair n s r).1 high)) j

/-- Each pin is either one designated local pin or a literal Boolean. -/
def wire (n s w : ℕ) (_hw : w ≤ n+s) :
    Fin (pins (n+s) (n+s)) → (Row s × Fin (pins n w)) ⊕ Bool :=
  select n s w ∘ (portIndex (n+s) (n+s)).symm

private def blockTag {n s : ℕ} (f : Row s → Row n → Row n) (r : Row (n+s)) :=
  (rowPair n s).symm ((rowPair n s r).1,f (rowPair n s r).1 (rowPair n s r).2)

private theorem bijective_blocks {n s : ℕ} (f : Row s → Row n → Row n) :
    Function.Bijective (blockTag f) ↔ ∀ a, Function.Bijective (f a) := by
  simp only [← Finite.injective_iff_bijective]
  let e := rowPair n s
  constructor
  · intro inj a i j hij
    have eqn : e.symm (a,i) = e.symm (a,j) := inj (by
      change e.symm ((e (e.symm (a,i))).1,f (e (e.symm (a,i))).1 (e (e.symm (a,i))).2) =
        e.symm ((e (e.symm (a,j))).1,f (e (e.symm (a,j))).1 (e (e.symm (a,j))).2)
      simp [hij])
    exact congrArg Prod.snd (e.symm.injective eqn)
  · intro inj i j hij
    have he := e.symm.injective hij
    have fst := congrArg (fun z : Row s × Row n => z.1) he
    have snd := congrArg (fun z : Row s × Row n => z.2) he
    change (e i).1=(e j).1 at fst
    change f (e i).1 (e i).2=f (e j).1 (e j).2 at snd
    rw [fst] at snd
    exact e.injective (Prod.ext fst (inj _ snd))

private theorem valid_blocks {n s w : ℕ} (hw : w ≤ n+s)
    (src dst : Row s → Row n → Bits w) (f : Row s → Row n → Row n) :
    Valid (fun r => pad hw (src (rowPair n s r).1 (rowPair n s r).2)) (blockTag f)
      (fun r => pad hw (dst (rowPair n s r).1 (rowPair n s r).2)) ↔
        ∀ a, Valid (src a) (f a) (dst a) := by
  constructor
  · rintro ⟨hb,hd⟩ a
    refine ⟨(bijective_blocks f).mp hb a,fun i => (pad hw).injective ?_⟩
    simpa [blockTag] using hd ((rowPair n s).symm (a,i))
  · intro ok
    refine ⟨(bijective_blocks f).mpr (fun a => (ok a).1),fun r => ?_⟩
    simpa only [blockTag,Equiv.apply_symm_apply] using
      congrArg (pad hw) ((ok (rowPair n s r).1).2 (rowPair n s r).2)

/-- All blocks are checked independently by the one large tagged coefficient. -/
theorem full_eval (F : Type*) [CommMonoidWithZero F] (n s w : ℕ) (hw : w ≤ n+s)
    (x : Row s × Fin (pins n w) → Bool) :
    coeff F (n+s) (n+s) (Sum.elim x id ∘ wire n s w hw) =
      ∏ a : Row s, coeff F n w (fun j => x (a,j)) := by
  let y := Sum.elim x id ∘ wire n s w hw
  let localPin := fun (a : Row s) (j : Fin (pins n w)) => x (a,j)
  have src : source y = fun r =>
      pad hw (source (localPin (rowPair n s r).1) (rowPair n s r).2) := by
    funext r j
    by_cases h : j.val<w <;>
      simp [source,y,wire,select,payload,pad,widenRecord,h,localPin]
  have dst : target y = fun r =>
      pad hw (target (localPin (rowPair n s r).1) (rowPair n s r).2) := by
    funext r j
    by_cases h : j.val<w <;>
      simp [target,y,wire,select,payload,pad,widenRecord,h,localPin]
  have key : tag y = blockTag (fun a => tag (localPin a)) := by
    funext r
    apply (wordBits (n+s)).injective
    change wordBits _ ((wordBits _).symm _) = wordBits _ ((wordBits _).symm _)
    simp only [Equiv.apply_symm_apply]
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [y,wire,select,tag,localPin]
  change coeff F (n+s) (n+s) y = ∏ a, coeff F n w (localPin a)
  simp only [coeff,src,dst,key,Fintype.prod_boole]
  rw [propext (valid_blocks hw (fun a => source (localPin a))
    (fun a => target (localPin a)) (fun a => tag (localPin a)))]
  by_cases valid : ∀a,Valid (source (localPin a)) (tag (localPin a)) (target (localPin a)) <;> simp [valid]

/-- A filler block fixes the identity permutation and two zero payload arrays. -/
def identityInput (n w : ℕ) : Fin (pins n w) → Bool :=
  (Sum.elim (fun _ => false) (Sum.elim (fun p => wordBits n p.1 p.2) (fun _ => false))) ∘
    (portIndex n w).symm

theorem identity_valid (n w : ℕ) : Valid (source (identityInput n w))
    (tag (identityInput n w)) (target (identityInput n w)) := by
  have eqn : tag (identityInput n w) = id := by
    funext r
    simp [tag,identityInput]
  rw [eqn]
  refine ⟨Function.bijective_id,fun r => ?_⟩
  funext j
  simp [target,source,identityInput]

theorem identity_eval (F : Type*) [Zero F] [One F] (n w : ℕ) :
    coeff F n w (identityInput n w) = 1 := by
  simp only [coeff,ite_eq_left (identity_valid n w)]

/-- Read a true call from the initial segment, or fill a surplus slot with literals. -/
def prefixPin (n w q : ℕ) {m : ℕ} (p : Fin m × Fin (pins n w)) :
    (Fin q × Fin (pins n w)) ⊕ Bool :=
  if active : p.1.val<q then .inl (⟨p.1.val,active⟩,p.2) else .inr (identityInput n w p.2)

theorem prefix_eval (F : Type*) [CommMonoidWithZero F] (n w q m : ℕ) (hq : q ≤ m)
    (x : Fin q × Fin (pins n w) → Bool) :
    (∏ i : Fin m, coeff F n w (fun j => Sum.elim x id (prefixPin n w q (i,j)))) =
      ∏ a : Fin q, coeff F n w (fun j => x (a,j)) := by
  simp only [coeff,Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro valid a
    simpa [prefixPin,a.isLt] using valid (a.castLE hq)
  · intro valid i
    by_cases h : i.val<q
    · simpa [prefixPin,h] using valid (⟨i.val,h⟩ : Fin q)
    · simpa [prefixPin,h] using identity_valid n w

def shortWire (n s w q : ℕ) (hw : w ≤ n+s) (_hq : q ≤ 2^s) :
    Fin (pins (n+s) (n+s)) → (Fin q × Fin (pins n w)) ⊕ Bool :=
  Sum.elim (prefixPin n w q) Sum.inr ∘ wire n s w hw

theorem short_eval (F : Type*) [CommMonoidWithZero F] (n s w q : ℕ) (hw : w ≤ n+s)
    (hq : q ≤ 2^s) (x : Fin q × Fin (pins n w) → Bool) :
    coeff F (n+s) (n+s) (Sum.elim x id ∘ shortWire n s w q hw hq) =
      ∏ a : Fin q, coeff F n w (fun j => x (a,j)) := by
  have expand : Sum.elim x id ∘ shortWire n s w q hw hq =
      Sum.elim (Sum.elim x id ∘ prefixPin n w q) id ∘ wire n s w hw := by
    funext j
    cases hj : wire n s w hw j <;> simp [shortWire,Function.comp_def,hj]
  rw [expand,full_eval]
  exact prefix_eval F n w q (2^s) hq x

end Hierarchy.Tagged.TerminalPack

end OAI
