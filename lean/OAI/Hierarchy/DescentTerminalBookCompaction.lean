import OAI.Hierarchy.DescentTerminalBookTokens

namespace OAI
/-! # Tabulating all six port-book fields in the two physical orders -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section

/-- The two indices below are original socket and original group-block slot.
Their holes are retained up to the shared table. A present vertex can have arity zero. -/
structure Directory (G V A:ℕ) where
  pieces : Fin G→ℕ
  venue : Fin V→Option ℕ
  address : Fin V→Fin A→Option (Fin G×ℕ)

def occupied {m:ℕ} (flag:Fin m→Prop) [DecidablePred flag] := Finset.univ.filter flag
def prior {m:ℕ} (valid:Finset (Fin m)) (x:Fin m) := (valid.filter (·<x)).card
def seek {m:ℕ} (valid:Finset (Fin m)) (k:ℕ) : Option (Fin m) :=
  if h:∃x,x∈valid ∧ prior valid x=k then some h.choose else none

theorem prior_strict {m:ℕ} {valid:Finset (Fin m)} {u v:Fin m} (hu:u∈valid) (lt:u<v) :
    prior valid u<prior valid v := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨fun i hi=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.trans lt⟩,fun eqn=>by
    have mem:u∈valid.filter (·<v):=Finset.mem_filter.mpr ⟨hu,lt⟩
    rw [←eqn] at mem
    exact lt_irrefl _ (Finset.mem_filter.mp mem).2⟩

theorem seek_at {m:ℕ} {valid:Finset (Fin m)} {u:Fin m} (hu:u∈valid) :
    seek valid (prior valid u)=some u := by
  have hit:∃x,x∈valid ∧ prior valid x=prior valid u:=⟨u,hu,rfl⟩
  rw [seek,dite_eq_left hit]
  apply congrArg some
  rcases lt_trichotomy hit.choose u with h|h|h
  · exact False.elim ((prior_strict hit.choose_spec.1 h).ne hit.choose_spec.2)
  · exact h
  · exact False.elim ((prior_strict hu h).ne hit.choose_spec.2.symm)

theorem seek_over {m:ℕ} (valid:Finset (Fin m)) (k:ℕ) (large:valid.card≤k) : seek valid k=none := by
  have missing : ¬ ∃ x, x ∈ valid ∧ prior valid x = k := by
    rintro ⟨x, hx, rank⟩
    have sub : valid.filter (· < x) ⊂ valid :=
      Finset.filter_ssubset.mpr ⟨x, hx, lt_irrefl x⟩
    have small : prior valid x < valid.card := Finset.card_lt_card sub
    exact (Nat.not_lt_of_ge large) (rank ▸ small)
  simp only [seek, dite_eq_right missing]

theorem prior_image {n m:ℕ} (f:Fin n↪Fin m) (ordered:StrictMono f) (i:Fin n) :
    prior (Finset.univ.map f) (f i)=i.val := by
  have eqn:(Finset.univ.map f).filter (·<f i)=(Finset.Iio i).map f:=by
    ext y
    simp only [Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_Iio]
    constructor
    · rintro ⟨⟨x,rfl⟩,lt⟩;exact ⟨x,ordered.lt_iff_lt.mp lt,rfl⟩
    · rintro ⟨x,lt,rfl⟩;exact ⟨⟨_,rfl⟩,ordered lt⟩
  simp [prior,eqn]

def Directory.activeGroups {G V A:ℕ} (d:Directory G V A) := occupied fun j=>0<d.pieces j
def Directory.activeNodes {G V A:ℕ} (d:Directory G V A) := occupied fun i=>(d.venue i).isSome=true

def Directory.sizes {G V A:ℕ} (d:Directory G V A) (n:ℕ) : ℕ :=
  (seek d.activeGroups n).elim 0 d.pieces
def Directory.arities {G V A:ℕ} (d:Directory G V A) (n:ℕ) : ℕ :=
  ((seek d.activeNodes n).bind d.venue).getD 0
def Directory.refs {G V A:ℕ} (d:Directory G V A) (M n:ℕ) (j:Fin A) : ℕ :=
  if j.val<d.arities n then ((seek d.activeNodes n).bind (fun v=>d.address v j)).elim 0
    (fun w=>prior d.activeGroups w.1*M+w.2) else 0

def clipped (K x:ℕ) : Fin (K+1) := ⟨min K x,by omega⟩
open Fin.NatCast in
def Directory.book {G V A:ℕ} (d:Directory G V A) (M:ℕ) : Book G V M A (nameBits G M) where
  groupCount:=clipped G d.activeGroups.card
  nodeCount:=clipped V d.activeNodes.card
  groupSize g:=clipped M (d.sizes g.val)
  nodeArity v:=clipped A (d.arities v.val)
  portName g j:=if j.val<d.sizes g.val then ((g.val*M+j.val:ℕ):Word (nameBits G M)) else 0
  operand v j:=((d.refs M v.val j:ℕ):Word (nameBits G M))

structure Aligned {G V A:ℕ} (t:Site) (d:Directory G V A) where
  group : Fin t.groups↪Fin G
  node : Fin t.nodes↪Fin V
  groupOrder : StrictMono group
  nodeOrder : StrictMono node
  groupSet : d.activeGroups=Finset.univ.map group
  nodeSet : d.activeNodes=Finset.univ.map node
  pieces : ∀g,d.pieces (group g)=t.size g
  venue : ∀v,d.venue (node v)=some (t.arity v)
  address : ∀v (j:Fin (t.arity v)) (a:Fin A),j.val=a.val→
    d.address (node v) a=some (group (t.arg v j).1,(t.arg v j).2.val)

namespace Aligned
variable {G V A M:ℕ} {t:Site} {d:Directory G V A} (h:Aligned t d)
include h in
theorem groups : d.activeGroups.card=t.groups := by simp [h.groupSet]
include h in
theorem nodes : d.activeNodes.card=t.nodes := by simp [h.nodeSet]
theorem socket (g:Fin t.groups):seek d.activeGroups g.val=some (h.group g) := by
  rw [h.groupSet,←prior_image h.group h.groupOrder g]
  exact seek_at (Finset.mem_map.mpr ⟨g,Finset.mem_univ _,rfl⟩)
theorem resident (v:Fin t.nodes):seek d.activeNodes v.val=some (h.node v) := by
  rw [h.nodeSet,←prior_image h.node h.nodeOrder v]
  exact seek_at (Finset.mem_map.mpr ⟨v,Finset.mem_univ _,rfl⟩)
include h in
theorem piece_count (g:ℕ) : d.sizes g=if hg:g<t.groups then t.size ⟨g,hg⟩ else 0 := by
  by_cases hg:g<t.groups
  · simp [Directory.sizes,h.socket ⟨g,hg⟩,hg,h.pieces]
  · have beyond : d.activeGroups.card ≤ g := h.groups.le.trans (Nat.le_of_not_gt hg)
    simp [Directory.sizes,seek_over d.activeGroups g beyond,hg]
include h in
theorem node_arity (v:ℕ) : d.arities v=if hv:v<t.nodes then t.arity ⟨v,hv⟩ else 0 := by
  by_cases hv:v<t.nodes
  · simp [Directory.arities,h.resident ⟨v,hv⟩,hv,h.venue]
  · have beyond : d.activeNodes.card ≤ v := h.nodes.le.trans (Nat.le_of_not_gt hv)
    simp [Directory.arities,seek_over d.activeNodes v beyond,hv]
include h in
theorem ref_at (M:ℕ) (v:Fin t.nodes) (j:Fin (t.arity v)) (a:Fin A) (same:j.val=a.val) :
    d.refs M v.val a=(t.arg v j).1.val*M+(t.arg v j).2.val := by
  have size:d.arities v.val=t.arity v:=by simp [h.node_arity,v.isLt]
  have small:a.val<d.arities v.val:=by rw [size,←same];exact j.isLt
  simp [Directory.refs,small,h.resident,h.address v j a same,h.groupSet,prior_image h.group h.groupOrder]

private theorem eq_book {g v m a b : ℕ} (x y : Book g v m a b)
    (p:x.groupCount=y.groupCount) (q:x.nodeCount=y.nodeCount)
    (r:x.groupSize=y.groupSize) (s:x.nodeArity=y.nodeArity)
    (u:x.portName=y.portName) (z:x.operand=y.operand) : x=y := by
  cases x;cases y;simp_all

include h in
theorem authentic (f:Room t G V M A) :
    d.book M=issue t f (rowName t f) (refName t f) := by
  apply eq_book
  · apply Fin.ext;simp [Directory.book,issue,clipped,h.groups,Nat.min_eq_right f.groups]
  · apply Fin.ext;simp [Directory.book,issue,clipped,h.nodes,Nat.min_eq_right f.nodes]
  · funext g;apply Fin.ext;by_cases hg:g.val<t.groups
    · simp [Directory.book,issue,clipped,h.piece_count,hg,Nat.min_eq_right (f.size _)]
    · simp [Directory.book,issue,clipped,h.piece_count,hg]
  · funext v;apply Fin.ext;by_cases hv:v.val<t.nodes
    · simp [Directory.book,issue,clipped,h.node_arity,hv,Nat.min_eq_right (f.arity _)]
    · simp [Directory.book,issue,clipped,h.node_arity,hv]
  · funext g j;apply Fin.ext
    by_cases hg:g.val<t.groups
    · by_cases hj:j.val<t.size ⟨g.val,hg⟩
      · have fit: g.val*M+j.val<2^nameBits G M:=(rowName t f ⟨⟨g.val,hg⟩,⟨j.val,hj⟩⟩).isLt
        simp [Directory.book,issue,h.piece_count,hg,hj,rowName,Fin.val_cast_of_lt fit]; rfl
      · simp [Directory.book,issue,h.piece_count,hg,hj]
    · simp [Directory.book,issue,h.piece_count,hg]
  · funext v a
    by_cases hv:v.val<t.nodes
    · let u : Fin t.nodes:=⟨v.val,hv⟩
      by_cases ha:a.val<t.arity u
      · let j:Fin (t.arity u):=⟨a.val,ha⟩
        have small : a.val < t.arity ⟨v.val, hv⟩ := ha
        have val : d.refs M v.val a = (t.arg u j).1.val*M+(t.arg u j).2.val :=
          h.ref_at M u j a rfl
        have fit: (t.arg u j).1.val*M+(t.arg u j).2.val<2^nameBits G M:=(rowName t f (t.arg u j)).isLt
        apply Fin.ext
        simp only [Directory.book,issue,dite_eq_left hv,dite_eq_left small]
        change d.refs M v.val a % (2^nameBits G M) = (t.arg u j).1.val*M+(t.arg u j).2.val
        rw [val, Nat.mod_eq_of_lt fit]
      · simp [Directory.book,issue,Directory.refs,h.node_arity,hv,u,ha]
    · simp [Directory.book,issue,Directory.refs,h.node_arity,hv]

end Aligned
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
