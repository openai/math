import OAI.Hierarchy.DescentDonorSiteOrder
import OAI.Hierarchy.DescentCableDonorNames
import OAI.Hierarchy.DescentCommonGroups
import OAI.Hierarchy.DescentHaloRankRAM

namespace OAI
/-! # Dynamic public walk ranks give authentic short old-donor tickets -/
namespace Hierarchy.DescentHaloDonorChart
open DescentHaloWalkRAM DescentOrdinaryDonorHalo DescentCableDonorNames DescentColonies DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {V U J A : Type} [DecidableEq V] [Fintype U] {H D k : ℕ}
variable (R : Fin H→Fin D→Option (Fin H))

theorem walk_congr (v : Fin H) (p q : Path D) (t : ℕ) (same : ∀j : Fin 4,j.val<t→p j=q j) : walk R v p t=walk R v q t :=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    have e:=ih (fun j h=>same j (by omega))
    by_cases ht : t<4
    · simp only [walk,dite_eq_left ht,e,same ⟨t,ht⟩ (Nat.lt_succ_self _)]
    · simp only [walk,dite_eq_right ht,e]

/-- The purchased one-hop roster supplies every real length-four path,
including stays used when the donor is nearer than the four-hop bound. -/
theorem reached (near : V→Finset V) (name : V↪Fin H)
    (member : ∀v u,u∈near v→∃i,R (name v) i=some (name u)) (t : ℕ) (height : t≤4) (v u : V)
    (inside : u∈around near t v) : ∃p : Path D,walk R (name v) p t=some (name u) :=by
  induction t generalizing u with
  | zero=>
    have eqn : u=v:=by simpa [around] using inside
    subst u
    exact ⟨fun _=>Fin.last D,rfl⟩
  | succ t ih=>
    obtain ⟨previous,atOld,next⟩:=Finset.mem_biUnion.mp inside
    obtain ⟨p,arrived⟩:=ih (by omega) previous atOld
    let last : Fin 4:=⟨t,by omega⟩
    have follow (j : Fin (D+1)) : walk R (name v) (Function.update p last j) (t+1)=step R (some (name previous)) j :=by
      have unchanged : walk R (name v) (Function.update p last j) t=walk R (name v) p t:=
        walk_congr R _ _ _ _ (fun a earlier=>Function.update_of_ne (by intro eqn;have:=congrArg Fin.val eqn;change a.val=t at this;omega) ..)
      have ht : t<4:=by omega
      simp only [walk,dite_eq_left ht,unchanged,arrived]
      change step R (some (name previous)) (Function.update p last j last)=_
      rw [Function.update_self]
    rcases Finset.mem_insert.mp next with stay|move
    · subst u;exact ⟨Function.update p last (Fin.last D),(follow (Fin.last D)).trans (by simp [step])⟩
    · obtain ⟨j,read⟩:=member previous u move
      exact ⟨Function.update p last j.castSucc,(follow j.castSucc).trans (by simpa [step,j.isLt] using read)⟩

def endpoint (v : Fin H) (p : Fin (breadth D)):=number (walk R v (path p) 4)

theorem encoded {r u : Fin H} {p : Path D} (hit : walk R r p 4=some u) : endpoint R r (finFunctionFinEquiv p)=u.val :=by
  simp [endpoint,path,hit,number]

/-- The semantic rank is exactly the word in *every* path slot which reaches
the donor. Duplicated walks only create gaps between different ranks. -/
def rank (v u : Fin H) (inside : ∃p : Path D,walk R v p 4=some u) : Fin (breadth D):=
  ⟨Ranks.earlier (endpoint R) v u.val,by obtain ⟨p,h⟩:=inside;rw [←encoded R h];exact Ranks.bound ..⟩

theorem rank_lt (v a b : Fin H) (ai : ∃p : Path D,walk R v p 4=some a) (bi : ∃p : Path D,walk R v p 4=some b) :
    rank R v a ai<rank R v b bi ↔ a<b :=by
  change Ranks.earlier _ _ a.val<Ranks.earlier _ _ b.val ↔ a.val<b.val
  obtain ⟨p,h⟩:=ai;obtain ⟨q,j⟩:=bi
  rw [←encoded R h,←encoded R j];exact Ranks.compare ..

def chart (members : A→Finset U) (root : A→Fin H) (donor : U→Fin H) (block : U→Block k)
    (coord : ∀a (u v : ↥(members a)),donor u.val=donor v.val→block u.val=block v.val→u=v)
    (inside : ∀a (u : ↥(members a)),∃p : Path D,walk R (root a) p 4=some (donor u.val)) :
    Halo A U (breadth D*2^k) where
  member:=members
  slot a:=
    {toFun:=fun u=>finProdFinEquiv (rank R (root a) (donor u.val) (inside a u),block u.val)
     inj':=by
      intro u v eqn;have part:=finProdFinEquiv.injective eqn;have rk:=congrArg Prod.fst part
      apply coord a u v _ (congrArg Prod.snd part)
      rcases lt_trichotomy (donor u.val) (donor v.val) with l|e|r
      · exact False.elim (((rank_lt R _ _ _ (inside a u) (inside a v)).2 l).ne rk)
      · exact e
      · exact False.elim (((rank_lt R _ _ _ (inside a v) (inside a u)).2 r).ne rk.symm)}

omit [Fintype U] in
theorem chart_lt (members : A→Finset U) (root : A→Fin H) (donor : U→Fin H) (block : U→Block k)
    (coord : ∀a (u v : ↥(members a)),donor u.val=donor v.val→block u.val=block v.val→u=v)
    (inside : ∀a (u : ↥(members a)),∃p : Path D,walk R (root a) p 4=some (donor u.val))
    (a : A) (u v : ↥(members a)) :
    (chart R members root donor block coord inside).slot a u<(chart R members root donor block coord inside).slot a v ↔
      (donor u.val).val*2^k+(block u.val).val<(donor v.val).val*2^k+(block v.val).val :=by
  let r:=fun z : ↥(members a)=>rank R (root a) (donor z.val) (inside a z)
  have cmp : r u<r v ↔ donor u.val<donor v.val:=rank_lt ..
  have eqv : r u=r v ↔ donor u.val=donor v.val:=by
    constructor
    · intro eqn;rcases lt_trichotomy (donor u.val) (donor v.val) with l|e|g
      · exact False.elim ((cmp.2 l).ne eqn)
      · exact e
      · exact False.elim (((rank_lt R _ _ _ (inside a v) (inside a u)).2 g).ne eqn.symm)
    · intro e;apply Fin.ext;change Ranks.earlier _ _ (donor u.val).val=Ranks.earlier _ _ (donor v.val).val;rw [e]
  change (finProdFinEquiv (r u,block u.val):Fin (breadth D*2^k))<finProdFinEquiv (r v,block v.val) ↔ _
  have numeric : (r u).val*2^k+(block u.val).val<(r v).val*2^k+(block v.val).val ↔
      (donor u.val).val*2^k+(block u.val).val<(donor v.val).val*2^k+(block v.val).val :=by
    simp only [DescentOrdinaryDonorHalo.lex (block u.val).isLt (block v.val).isLt]
    exact or_congr cmp (and_congr_left' (by simpa only [Fin.ext_iff] using eqv))
  simpa only [Fin.lt_def,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using numeric

/-- Membership of a grouped real site carries its group equality and a true
walk in the single shared physical host graph. -/
theorem common [DecidableEq J] (near : V→Finset V) (t : ℕ) (a b : J×V)
    (inside : b∈around (groupedNear near) t a) : b.1=a.1 ∧ b.2∈around near t a.2 :=by
  induction t generalizing b with
  | zero=>
    have eqn : b=a:=by simpa [around] using inside
    subst b
    exact ⟨rfl,by simp [around]⟩
  | succ t ih=>
    obtain ⟨u,visited,hop⟩:=Finset.mem_biUnion.mp inside
    obtain ⟨grp,old⟩:=ih u visited
    rcases Finset.mem_insert.mp hop with stay|go
    · subst b;exact ⟨grp,Finset.mem_biUnion.mpr ⟨u.2,old,Finset.mem_insert_self ..⟩⟩
    · obtain ⟨v,edge,arrived⟩:=Finset.mem_map.mp go
      exact ⟨(congrArg Prod.fst arrived).symm.trans grp,Finset.mem_biUnion.mpr ⟨u.2,old,
        Finset.mem_insert_of_mem (by rw [←arrived]; exact edge)⟩⟩

end
end Hierarchy.DescentHaloDonorChart

/-! # The common finite halo and actual donor ordinal of each named source -/
namespace Hierarchy.DescentHaloCompilation
open DescentHaloWalkRAM DescentHaloDonorChart DescentCableDonorNames DescentOrdinaryDonorHalo
open DescentColonies DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {H D w k : ℕ} {F P J V U : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
variable (near : V→Finset V) (name : V↪Fin H) (R : Fin H→Fin D→Option (Fin H))
variable (listed : ∀v u,u∈near v→∃i,R (name v) i=some (name u))
variable (pos : U→J×V) (block : U→Block k) (coord : Function.Injective fun u=>(pos u,block u))
include coord in
private theorem one (s : Key (J×V)) (u v : ↥((siteSet (groupedNear near) pos) s)) (rack : (fun u : U=>name (pos u).2) u.val=(fun u : U=>name (pos u).2) v.val) (grain : block u.val=block v.val) :u=v:=by
  have left:=common near 4 s.1 (pos u.val) (Finset.mem_filter.mp u.property).2
  have right:=common near 4 s.1 (pos v.val) (Finset.mem_filter.mp v.property).2
  exact Subtype.ext (coord (Prod.ext (Prod.ext (left.1.trans right.1.symm) (name.injective rack)) grain))

include listed in
private theorem visits (s : Key (J×V)) (u : ↥((siteSet (groupedNear near) pos) s)) : ∃p : Path D,walk R ((fun x : Key (J×V)=>name x.1.2) s) p 4=some ((fun u : U=>name (pos u).2) u.val) :=
  reached R near name listed 4 le_rfl s.1.2 (pos u.val).2 (common near 4 s.1 (pos u.val) (Finset.mem_filter.mp u.property).2).2

def shared := chart R (siteSet (groupedNear near) pos) (fun x : Key (J×V)=>name x.1.2) (fun u : U=>name (pos u).2) block (one near name pos block coord) (visits near name R listed pos)

theorem ordered (s : Key (J×V)) (u v : ↥((siteSet (groupedNear near) pos) s)) :
    (shared near name R listed pos block coord).slot s u<(shared near name R listed pos block coord).slot s v ↔
      (name (pos u.val).2).val*2^k+(block u.val).val<(name (pos v.val).2).val*2^k+(block v.val).val :=
  chart_lt R (siteSet (groupedNear near) pos) (fun x : Key (J×V)=>name x.1.2) (fun u : U=>name (pos u).2) block (one near name pos block coord) (visits near name R listed pos) s u v

/-- Every new normalized source uses the very same common physical rack
header. Changing the new site key only changes the selected rack row. -/
def atSource {A : Type} (srcKey : A→Key (J×V)) : Halo A U (breadth D*2^k) where
  member s:=(siteSet (groupedNear near) pos) (srcKey s)
  slot s:=(shared near name R listed pos block coord).slot (srcKey s)

end
end Hierarchy.DescentHaloCompilation

end OAI
