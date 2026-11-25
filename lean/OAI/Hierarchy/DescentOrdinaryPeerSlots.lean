import OAI.Hierarchy.DescentOrdinaryPeerChart
import Mathlib.Data.Finset.Sort

namespace OAI
/-! The ordinal of a sorted Cartesian product uses consecutive local shape
slots for each reachable old host. Empty shape sets and padded rows are blank. -/
namespace Hierarchy.DescentOrdinaryPeerSlots
open DescentOrdinaryPeerLifts
open scoped Classical
noncomputable section

variable {H P S R D : ℕ}

def requestAt (shapes : Fin S→Finset (Fin S)) (v : Fin H) (q : Fin S) (j : ℕ) :
    Option (Entry H P S) :=
  let a:=shapes q
  if ok : 0<a.card ∧ j/a.card<P then
    some ⟨v,⟨j/a.card,ok.2⟩,a.orderEmbOfFin rfl ⟨j%a.card,Nat.mod_lt _ ok.1⟩⟩
  else none

def atRow (shapes : Fin S→Finset (Fin S)) (x : Fin R) (i : Fin D) : Option (Entry H P S) :=
  if valid : x.val<H*S then
    let p:=finProdFinEquiv.symm (⟨x.val,valid⟩ : Fin (H*S))
    requestAt shapes p.1 p.2 i.val
  else none

def request (shapes : Fin S→Finset (Fin S)) : Request H P S (R*D) :=
  fun i=>let p:=finProdFinEquiv.symm i; atRow shapes p.1 p.2

def code (v : Fin H) (q : Fin S) : Fin (H*S) := finProdFinEquiv (v,q)

theorem code_val (v : Fin H) (q : Fin S) : (code v q).val=v.val*S+q.val := by
  simp [code,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]

theorem named (shapes : Fin S→Finset (Fin S)) (x : Fin R) (i : Fin D) (v : Fin H) (q : Fin S)
    (h : x.val=(code v q).val) :
    request (P:=P) shapes (finProdFinEquiv (x,i))=requestAt shapes v q i.val := by
  have live : x.val<H*S:=by rw [h]; exact (code v q).isLt
  have eqn : (⟨x.val,live⟩:Fin (H*S))=code v q:=Fin.ext h
  simp [request,atRow,live,eqn,code]

def entry (a : Finset (Fin H)) (b : Finset (Fin S)) (j : ℕ) : Option (Fin H × Fin S) :=
  if yes : j<a.card*b.card then
    have pos : 0<b.card:=by by_contra! h;rw [Nat.eq_zero_of_le_zero h,Nat.mul_zero] at yes;omega
    some (a.orderEmbOfFin rfl ⟨j/b.card,(Nat.div_lt_iff_lt_mul pos).2 yes⟩,
      b.orderEmbOfFin rfl ⟨j%b.card,Nat.mod_lt _ pos⟩)
  else none

def selected (a : Finset (Fin H)) (b : Finset (Fin S)) (j : Fin (a.card*b.card)) : Fin H×Fin S :=
  (a.orderEmbOfFin rfl j.divNat,b.orderEmbOfFin rfl j.modNat)

theorem entry_selected (a : Finset (Fin H)) (b : Finset (Fin S)) (j : Fin (a.card*b.card)) :
    entry a b j.val=some (selected a b j) := by
  rw [entry,dite_eq_left j.isLt]; rfl

theorem selected_mem (a : Finset (Fin H)) (b : Finset (Fin S)) (j : Fin (a.card*b.card)) :
    (selected a b j).1∈a ∧ (selected a b j).2∈b :=
  ⟨(a.orderIsoOfFin rfl j.divNat).property,(b.orderIsoOfFin rfl j.modNat).property⟩

private theorem digit_lt {a b i j radix : ℕ} (hi : i<radix) (hj : j<radix) :
    a*radix+i<b*radix+j ↔ a<b ∨ (a=b ∧ i<j) := by
  rcases lt_trichotomy a b with lt|eq|gt
  · have step:=Nat.mul_le_mul_right radix lt
    rw [Nat.succ_mul] at step
    omega
  · subst b;omega
  · have step:=Nat.mul_le_mul_right radix gt
    rw [Nat.succ_mul] at step
    omega

theorem selected_strict (a : Finset (Fin H)) (b : Finset (Fin S)) :
    StrictMono (fun j=>(code (selected a b j).1 (selected a b j).2).val) := by
  intro i j h
  have dec (x : Fin (a.card*b.card)) : x.val=x.divNat.val*b.card+x.modNat.val :=
    (congrArg Fin.val (finProdFinEquiv.apply_symm_apply x)).symm.trans (code_val x.divNat x.modNat)
  have lt : i.divNat<j.divNat ∨ (i.divNat=j.divNat ∧ i.modNat<j.modNat) := by
    have scalar : i.val<j.val:=h
    rw [dec i,dec j,digit_lt i.modNat.isLt j.modNat.isLt] at scalar
    exact scalar.imp_right (fun h=>⟨Fin.ext h.1,h.2⟩)
  change (code (selected a b i).1 (selected a b i).2).val <
    (code (selected a b j).1 (selected a b j).2).val
  simp only [code_val]
  apply (digit_lt (selected a b i).2.isLt (selected a b j).2.isLt).mpr
  rcases lt with x|⟨x,y⟩
  · exact Or.inl ((a.orderEmbOfFin rfl).strictMono x)
  · exact Or.inr ⟨congrArg (fun z=>(a.orderEmbOfFin rfl z).val) x,(b.orderEmbOfFin rfl).strictMono y⟩

theorem entry_iff (a : Finset (Fin H)) (b : Finset (Fin S)) (v : Fin H) (q : Fin S) :
    (∃j,entry a b j=some (v,q)) ↔ v∈a ∧ q∈b := by
  classical
  constructor
  · rintro ⟨j,hj⟩
    by_cases small : j<a.card*b.card
    · let i:Fin (a.card*b.card):=⟨j,small⟩
      have hit : selected a b i=(v,q):=Option.some.inj ((entry_selected a b i).symm.trans hj)
      simpa only [hit] using selected_mem a b i
    · simp [entry,small] at hj
  · rintro ⟨hv,hq⟩
    let i:=(a.orderIsoOfFin rfl).symm ⟨v,hv⟩
    let l:=(b.orderIsoOfFin rfl).symm ⟨q,hq⟩
    let z:=finProdFinEquiv (i,l)
    refine ⟨z.val,(entry_selected a b z).trans (congrArg some ?_)⟩
    change (a.orderEmbOfFin rfl (finProdFinEquiv.symm z).1,b.orderEmbOfFin rfl (finProdFinEquiv.symm z).2)=(v,q)
    simp only [z,Equiv.symm_apply_apply]
    exact Prod.ext (congrArg Subtype.val ((a.orderIsoOfFin rfl).apply_symm_apply _))
      (congrArg Subtype.val ((b.orderIsoOfFin rfl).apply_symm_apply _))

theorem computes (N R : ℕ) (ships : Fin H→Fin P→Option (Fin H)) (shapes : Fin S→Finset (Fin S))
    (v : Fin H) (q : Fin S) (j : ℕ) (live : v.val<N) (hosts : Finset (Fin H)) (cap : hosts.card≤P)
    (ordered : ∀i : Fin P,ships v i=if yes:i.val<hosts.card then some (hosts.orderEmbOfFin rfl ⟨i.val,yes⟩) else none) :
    result N R S ships (requestAt shapes v q j)=
      (entry hosts (shapes q) j).elim R (fun h=>h.1.val*S+h.2.val) := by
  classical
  let b:=shapes q
  by_cases yes : j<hosts.card*b.card
  · have bp : 0<b.card:=by by_contra! hh;rw [Nat.eq_zero_of_le_zero hh,Nat.mul_zero] at yes;omega
    have left : j/b.card<hosts.card:=(Nat.div_lt_iff_lt_mul bp).2 yes
    have ix:=left.trans_le cap
    have req : 0<(shapes q).card ∧ j/(shapes q).card<P:=⟨bp,ix⟩
    simp [requestAt,req,result,live,ordered,show j/(shapes q).card<hosts.card from left,
      entry,show j<hosts.card*(shapes q).card from yes]
  · by_cases room : 0<b.card ∧ j/b.card<P
    · have last : ¬j/b.card<hosts.card:=fun h=>yes ((Nat.div_lt_iff_lt_mul room.1).1 h)
      change _=(entry hosts b j).elim R _
      simp [requestAt,←show b=shapes q from rfl,room,result,ordered,live,last,entry,yes]
    · simp only [requestAt,←show b=shapes q from rfl,dite_eq_right room,entry,dite_eq_right yes,
        result,Option.elim_none]

theorem ghost (N R : ℕ) (ships : Fin H→Fin P→Option (Fin H)) (shapes : Fin S→Finset (Fin S))
    (v : Fin H) (q : Fin S) (j : ℕ) (padded : N≤v.val) :
    result N R S ships (requestAt shapes v q j)=R := by
  by_cases ok : 0<(shapes q).card ∧ j/(shapes q).card<P
  · simp only [requestAt,dite_eq_left ok,result,Option.elim_some,ite_eq_right (Nat.not_lt_of_ge padded)]
  · simp only [requestAt,dite_eq_right ok,result,Option.elim_none]


end
end Hierarchy.DescentOrdinaryPeerSlots

end OAI
