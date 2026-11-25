import OAI.Hierarchy.DescentParallelIncidentPosition
import OAI.Hierarchy.DescentPackedOperandStreamSerial
import OAI.Hierarchy.DescentHaloPairRanks

namespace OAI
/-! # Streamed source-grouped rank within the entire real two-sided panel -/
namespace Hierarchy.DescentParallelBase.Incidence
open DescentSharedCableNames DescentHaloWalkRAM
open scoped Classical BigOperators
noncomputable section
variable {U E : Type} [DecidableEq U] [Fintype E] {n cap m Q K : ℕ} {B : Ends U n} (C : Blocks B E)

/-- The same small two-record comparison LUT used for shared serials can
recover the entire incidence slot. All records here have one constant peer
and their priority is the common source key followed by its donor ticket. -/
def row (source : Fin Q) (ticket : Fin K) (weight : Fin (cap+1)) : Entry 1 (Q*K) cap :=
  ⟨0,false,finProdFinEquiv (source,ticket),weight⟩

theorem compare (s t : Fin Q) (a b : Fin K) (x y : Fin (cap+1)) : priority (row s a x)<priority (row t b y) ↔ s<t ∨ s=t ∧ a<b :=by
  have key (u : Fin Q) (c : Fin K) (weight : Fin (cap+1)) :
      priority (row u c weight) = u.val*K+c.val := by
    simp only [priority,row,Bool.toNat_false,Nat.zero_mul,Nat.zero_add,finProdFinEquiv_apply_val]
    ac_rfl
  rw [key,key,DescentOrdinaryDonorHalo.lex a.isLt b.isLt]
  simp only [Fin.lt_def,Fin.ext_iff]

theorem source_before {H P : ℕ} (reach : Fin H→Fin P→Option (Fin H)) (v u z t w : Fin H) (pa qa pb qb : Fin P)
    (toA : reach v pa=some u) (toB : reach v pb=some z) (fromA : reach u qa=some t) (fromB : reach z qb=some w) :
    PairRanks.ticket reach v pa qa<PairRanks.ticket reach v pb qb ↔ t<w :=by
  let endpoint := fun h s => number (PairRanks.combined reach h s)
  have left : endpoint v (PairRanks.pair pa qa) = t.val := by simp [endpoint,toA,fromA,number]
  have right : endpoint v (PairRanks.pair pb qb) = w.val := by simp [endpoint,toB,fromB,number]
  change Ranks.earlier endpoint v (endpoint v (PairRanks.pair pa qa)) <
    Ranks.earlier endpoint v (endpoint v (PairRanks.pair pb qb)) ↔ t.val < w.val
  exact (Ranks.compare endpoint v _ _).trans (by rw [left,right])

theorem streamed (h : U) (fit : ∀u,(B.incident u).card≤cap) (address : Local C h↪Fin m)
    (source : Local C h→Fin Q) (ticket : Local C h→Fin K) (mass : Local C h→Fin (cap+1))
    (weight : ∀e,(mass e).val=C.count e.val) (ordered : ∀e f,C.first e.val<C.first f.val ↔
      source e<source f ∨ source e=source f ∧ ticket e<ticket f) (e : Local C h) :
    let entry:=fun f=>row (source f) (ticket f) (mass f)
    (∑i:Fin m,Stream.qty (some (entry e)) (place address entry i))=(B.position fit h (candidate C h e ⟨0,e.property.1⟩)).val :=by
  intro entry;change base (place address entry) (entry e)=_
  rw [sum_place,initial C h fit e]
  let good (f:E):=0<C.count f ∧ (C.src f=h ∨ C.dst f=h)
  let cost (f:E):=if (C.src f=h ∨ C.dst f=h) ∧ C.first f<C.first e.val then C.count f else 0
  have occupy f (on:good f) : counted (entry e) (some (entry ⟨f,on⟩))=cost f:=by
    let x : Local C h:=⟨f,on⟩
    have rank : priority (entry x)<priority (entry e) ↔ C.first f<C.first e.val :=
      (compare (source x) (source e) (ticket x) (ticket e) (mass x) (mass e)).trans (ordered x e).symm
    change (if (entry x).peer=(entry e).peer ∧ priority (entry x)<priority (entry e)
      then (mass x).val else 0) = cost f
    have peer : (entry x).peer=(entry e).peer := rfl
    simp only [peer,eq_self,true_and,rank,weight,cost,on.2]
    by_cases earlier : C.first f<C.first e.val
    · simpa only [ite_eq_left earlier] using (show C.count x.val = C.count f from rfl)
    · simp only [ite_eq_right earlier]
  have all : ∑f:Local C h,counted (entry e) (some (entry f))=∑f:Local C h,cost f.val:=by
    apply Finset.sum_congr rfl;intro f _;exact occupy f.val f.property
  rw [all];change (∑f:{a:E//good a},cost f.val)=∑f:E,cost f
  rw [←Finset.sum_subtype (Finset.univ.filter good) (by simp) cost]
  apply Finset.sum_subset (Finset.subset_univ _);intro u _ no
  by_cases incident:C.src u=h ∨ C.dst u=h
  · have empty:C.count u=0:=by by_contra! pos;apply no;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.pos_of_ne_zero pos,incident⟩
    simp [cost,empty]
  · simp [cost,incident]

end
end Hierarchy.DescentParallelBase.Incidence

end OAI
