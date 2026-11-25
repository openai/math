import OAI.Hierarchy.DescentSharedCableSerial
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # A weighted local parent count equals the true shared first-grain serial -/
namespace Hierarchy.DescentParallelBase
open DescentSIMDLookup DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section
variable {E H : Type} [Fintype E] [DecidableEq H] {n : ℕ}

/-- All finer grains of one retained parent form a single interval in the
physical stream. The start may be arbitrary for an empty parent. -/
structure Blocks (B : Ends H n) (E : Type) where
  count : E→ℕ
  first : E→ℕ
  src : E→H
  dst : E→H
  order : (Σe,Fin (count e))≃Fin n
  atSource : ∀e j,B.src (order ⟨e,j⟩)=src e
  atTarget : ∀e j,B.dst (order ⟨e,j⟩)=dst e
  consecutive : ∀e j,(order ⟨e,j⟩).val=first e+j.val

namespace Blocks
variable {B : Ends H n} (C : Blocks B E)

def parallel (u v : H) (e : E) : Prop := (C.src e=u ∧ C.dst e=v) ∨ (C.src e=v ∧ C.dst e=u)

omit [Fintype E] [DecidableEq H] in
theorem disjoint {e f : E} (positive : 0<C.count f) (old : C.first e<C.first f) : C.first e+C.count e≤C.first f :=by
  by_contra! overlap
  let j : Fin (C.count e):=⟨C.first f-C.first e,by omega⟩
  let z : Fin (C.count f):=⟨0,positive⟩
  have shares : C.order ⟨e,j⟩=C.order ⟨f,z⟩:=by apply Fin.ext;rw [C.consecutive,C.consecutive];change C.first e+(C.first f-C.first e)=C.first f+0;omega
  have same : e=f:=congrArg Sigma.fst (C.order.injective shares)
  subst f;exact old.false

theorem first_serial (e : E) (positive : 0<C.count e) :
    B.serial (C.src e) (C.dst e) (C.order ⟨e,⟨0,positive⟩⟩)=
      ∑f : E,if C.parallel (C.src e) (C.dst e) f ∧ C.first f<C.first e then C.count f else 0 :=by
  let subset:=B.earlier (C.src e) (C.dst e) (C.order ⟨e,⟨0,positive⟩⟩)
  let char (r : Fin n):ℕ:=if r∈subset then 1 else 0
  change subset.card=_
  calc
    _=∑r : Fin n,char r:=by simp [char]
    _=∑s : Σf,Fin (C.count f),char (C.order s):=(Equiv.sum_comp C.order char).symm
    _=∑f : E,∑j : Fin (C.count f),char (C.order ⟨f,j⟩):=Fintype.sum_sigma _
    _= _:=by
      apply Finset.sum_congr rfl;intro f _
      have extract (j : Fin (C.count f)) : C.order ⟨f,j⟩∈subset ↔ C.parallel (C.src e) (C.dst e) f ∧ C.first f<C.first e :=by
        simp only [subset,Ends.earlier,Ends.parallel,Finset.mem_filter,Finset.mem_univ,true_and,C.atSource,C.atTarget,Fin.lt_def,C.consecutive,Nat.add_zero]
        have time : C.first f+j.val<C.first e ↔ C.first f<C.first e :=by
          constructor
          · omega
          · intro old;have:=C.disjoint positive old;have:=j.isLt;omega
        simp only [time,parallel];tauto
      by_cases prior : C.parallel (C.src e) (C.dst e) f ∧ C.first f<C.first e <;> simp [char,extract,prior]
end Blocks

/-- The comparison side is canonical: the lower ordered vertex of a pair
of distinct sites is the source of every cable in the first band. -/
structure Entry (D K L : ℕ) where
  peer : Fin D
  upper : Bool
  ticket : Fin K
  weight : Fin (L+1)

def priority {D K L} (x : Entry D K L):=x.upper.toNat*K+x.ticket.val

def counted {D K L} (query : Entry D K L) (other : Option (Entry D K L)) : ℕ:=
  other.elim 0 (fun o=>if o.peer=query.peer ∧ priority o<priority query then o.weight.val else 0)

def base {D K L m} (rows : Fin m→Option (Entry D K L)) (query : Entry D K L) := ∑j:Fin m,counted query (rows j)

/-- Install exactly the active positive parents resident at this endpoint
into the physical candidate aperture; unused candidate cells remain empty. -/
def place {X : Type} [Fintype X] {m D K L} (address : X↪Fin m) (row : X→Entry D K L) (j : Fin m) :=
  if hit : ∃f,address f=j then some (row hit.choose) else none

theorem place_at {X : Type} [Fintype X] {m D K L} (address : X↪Fin m) (row : X→Entry D K L) (i : X) : place address row (address i)=some (row i) :=by
  have hit : ∃f,address f=address i:=⟨i,rfl⟩;rw [place,dite_eq_left hit,address.injective hit.choose_spec]

theorem place_empty {X : Type} [Fintype X] {m D K L} (address : X↪Fin m) (row : X→Entry D K L) (j : Fin m)
    (no : ∀i,address i≠j):place address row j=none:=by simp [place,not_exists.mpr no]

theorem sum_place {X : Type} [Fintype X] {m D K L} (address : X↪Fin m) (row : X→Entry D K L) (query : Entry D K L) :
    base (place address row) query=∑i : X,counted query (some (row i)) :=by
  unfold base
  let active:=Finset.univ.map address
  have keep : ∑j:Fin m,counted query (place address row j)=∑j∈active,counted query (place address row j):=by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ outside
    have no : ∀i,address i≠j:=by intro i eqn;exact outside (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,eqn⟩)
    rw [place_empty address row j no];rfl
  rw [keep];simp [active,place_at]

variable {B : Ends H n} (C : Blocks B E) (h : H)
abbrev Local := {e : E // 0<C.count e ∧ (C.src e=h ∨ C.dst e=h)}
def other (e : Local C h) := if C.src e.val=h then C.dst e.val else C.src e.val

omit [Fintype E] in
theorem other_parallel (e f : Local C h) : C.parallel (C.src e.val) (C.dst e.val) f.val ↔ other C h f=other C h e :=by
  have ev:=e.property.2;have fv:=f.property.2
  unfold Blocks.parallel other;split <;> split <;> grind

/-- This theorem compares with the actual global `Ends.serial` over all
finer physical grains. The only numeric comparison in the local table is a
one-bit source orientation followed by a bounded donor ticket. -/
theorem authentic {D K L m} (address : Local C h↪Fin m) (row : Local C h→Entry D K L)
    (peer : ∀e f,(row e).peer=(row f).peer ↔ other C h e=other C h f)
    (order : ∀e f,other C h e=other C h f→(priority (row e)<priority (row f) ↔ C.first e.val<C.first f.val))
    (count : ∀e,(row e).weight.val=C.count e.val) (e : Local C h) :
    base (place address row) (row e)=B.serial (C.src e.val) (C.dst e.val) (C.order ⟨e.val,⟨0,e.property.1⟩⟩) :=by
  rw [sum_place,C.first_serial]
  let cost (f : E):=if C.parallel (C.src e.val) (C.dst e.val) f ∧ C.first f<C.first e.val then C.count f else 0
  have each (f : Local C h):counted (row e) (some (row f))=cost f.val:=by
    change (if (row f).peer=(row e).peer ∧ priority (row f)<priority (row e) then (row f).weight.val else 0)=_
    have eligible : ((row f).peer=(row e).peer ∧ priority (row f)<priority (row e)) ↔
        C.parallel (C.src e.val) (C.dst e.val) f.val ∧ C.first f.val<C.first e.val := by
      constructor
      · rintro ⟨same, earlier⟩
        have neighbor := (peer f e).mp same
        exact ⟨(other_parallel C h e f).mpr neighbor, (order f e neighbor).mp earlier⟩
      · rintro ⟨parallel, earlier⟩
        have neighbor := (other_parallel C h e f).mp parallel
        exact ⟨(peer f e).mpr neighbor, (order f e neighbor).mpr earlier⟩
    by_cases hit : (row f).peer=(row e).peer ∧ priority (row f)<priority (row e)
    · simp only [cost, ite_eq_left hit, ite_eq_left (eligible.mp hit), count]
    · simp only [cost, ite_eq_right hit, ite_eq_right (fun old => hit (eligible.mpr old))]
  simp_rw [each]
  change ∑f : Local C h,cost f.val=∑f : E,cost f
  rw [←Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (f:=cost) (p:=fun f=>0<C.count f ∧ (C.src f=h ∨ C.dst f=h))]
  have missing : ∑f∈Finset.univ.filter (fun f=>¬(0<C.count f ∧ (C.src f=h ∨ C.dst f=h))),cost f=0:=by
    apply Finset.sum_eq_zero;intro f no
    have no':= (Finset.mem_filter.mp no).2
    by_cases yes : C.parallel (C.src e.val) (C.dst e.val) f ∧ C.first f<C.first e.val
    · have ends:=yes.1;have here:=e.property.2
      have dead : C.count f=0:=by by_contra! pos;apply no';exact ⟨by omega,by unfold Blocks.parallel at ends;grind⟩
      simp [cost,yes,dead]
    · simp [cost,yes]
  rw [missing,Nat.add_zero];exact (Finset.sum_subtype _ (fun _=>by simp) _).symm

end
end Hierarchy.DescentParallelBase

end OAI
