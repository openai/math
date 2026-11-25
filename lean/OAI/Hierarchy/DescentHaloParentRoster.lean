import OAI.Hierarchy.DescentParallelBaseStream
import OAI.Hierarchy.DescentRawCableRoster

namespace OAI
/-! # The deduplicated two-sided receiver aperture for originally issued parent records -/
namespace Hierarchy.DescentParallelBase.Resident
open DescentSharedCableNames DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {U E X : Type} [DecidableEq U] [Fintype E] [Fintype X] {n H P O D K L : ℕ}
variable {B : Ends U n} (C : Blocks B E) (at_ : U) (host : U→Fin H)
variable (loc : X↪Fin H×Fin O) (raw : Local C at_↪X) (R : Fin H→Fin P→Option (Fin H))
variable (near : ∀e : Local C at_,∃j,R (host at_) j=some (loc (raw e)).1)

/-- The original `(group,old block,first outgoing, eleven-way role)` column
is unchanged by transfer. Its unbounded owner is replaced by one unique
short path, computed from the common physical topology. -/
def visit (e : Local C at_) : Fin P :=(Gather.once R (host at_) (loc (raw e)).1 (near e)).exists.choose

omit [DecidableEq U] [Fintype E] [Fintype X] in
theorem visit_read (e : Local C at_) : Gather.select R (host at_) (visit C at_ host loc raw R near e)=some (loc (raw e)).1 :=
  (Gather.once R (host at_) (loc (raw e)).1 (near e)).exists.choose_spec

def address : Local C at_↪Fin (P*O) where
  toFun e:=finProdFinEquiv (visit C at_ host loc raw R near e,(loc (raw e)).2)
  inj' :=by
    intro a b eqn;have pair:=finProdFinEquiv.injective eqn
    have seen:=congrArg (Gather.select R (host at_)) (congrArg Prod.fst pair)
    rw [visit_read,visit_read] at seen
    have slot := congrArg (fun x : Fin P × Fin O => x.2) pair
    exact raw.injective (loc.injective (Prod.ext (Option.some.inj seen) slot))

/-- A physical source column may contain many real parents that do not
survive at this receiving endpoint. Their local incidence test yields none. -/
def oldAt {Y : Type} (f : X→Option Y) (u : Fin H) (i : Fin O) :=if ok : ∃x,loc x=(u,i) then f ok.choose else none

theorem old_at {Y : Type} (f : X→Option Y) (x : X) : oldAt loc f (loc x).1 (loc x).2=f x :=by
  have hit:∃j,loc j=((loc x).1,(loc x).2):=⟨x,rfl⟩;rw [oldAt,dite_eq_left hit,loc.injective hit.choose_spec]

def fetched {Y : Type} (f : X→Option Y) (j : Fin (P*O)) :=
  let p:=finProdFinEquiv.symm j
  (Gather.select R (host at_) p.1).bind (fun u=>oldAt loc f u p.2)

def localRaw (row : Local C at_→Entry D K L) (x : X) : Option (Entry D K L) :=
  if live : ∃e : Local C at_,raw e=x then some (row live.choose) else none

omit [Fintype X] in
theorem live (row : Local C at_→Entry D K L) (e : Local C at_) : localRaw C at_ raw row (raw e)=some (row e) :=by
  have ok:∃f:Local C at_,raw f=raw e:=⟨e,rfl⟩;rw [localRaw,dite_eq_left ok,show ok.choose=e from raw.injective ok.choose_spec]

/-- Equality of complete native aperture, with all irrelevant original
edges, missing locations, repeated visits, and unused slot positions zero. -/
theorem entire (row : Local C at_→Entry D K L) (f : X→Option (Entry D K L)) (measured : ∀x,f x=localRaw C at_ raw row x) :
    fetched at_ host loc R f=place (address C at_ host loc raw R near) row :=by
  funext j;let a:=address C at_ host loc raw R near
  by_cases present:∃e,a e=j
  · obtain ⟨e,rfl⟩:=present
    have decoded : finProdFinEquiv.symm (a e) =
        (visit C at_ host loc raw R near e, (loc (raw e)).2) :=
      finProdFinEquiv.symm_apply_apply _
    rw [place_at]
    simp only [fetched, decoded, visit_read, Option.bind_some, old_at, measured, live]
  · rw [place_empty a row j (not_exists.mp present)]
    let p:=finProdFinEquiv.symm j
    change (Gather.select R (host at_) p.1).bind (fun u=>oldAt loc f u p.2)=none
    cases seen:Gather.select R (host at_) p.1 with
    | none=>rfl
    | some u=>
      change oldAt loc f u p.2=none
      unfold oldAt;split
      · rename_i found;let x:=found.choose;have orig:loc x=(u,p.2):=found.choose_spec
        rw [measured];unfold localRaw;split
        · rename_i mount;let e:=mount.choose;have stored:raw e=x:=mount.choose_spec
          have receiver : (loc (raw e)).1=u:=by rw [stored,orig]
          have src : Gather.select R (host at_) p.1=some (loc (raw e)).1:=by rw [receiver];exact seen
          have unique:=Gather.once R (host at_) (loc (raw e)).1 (near e)
          have same:=unique.unique (visit_read C at_ host loc raw R near e) src
          exfalso;apply present;refine ⟨e,?_⟩
          change finProdFinEquiv (visit C at_ host loc raw R near e,(loc (raw e)).2)=j
          rw [same,stored,orig];exact finProdFinEquiv.apply_symm_apply j
        · rfl
      · rfl

/-- The classifier may use the actual receiving path's reverse-rank header.
It is consulted only on original records resident at that path's rack. -/
def collected {Y : Type} (f : Fin P→X→Option Y) (j : Fin (P*O)) :=
  let p:=finProdFinEquiv.symm j
  (Gather.select R (host at_) p.1).bind (fun u=>oldAt loc (f p.1) u p.2)

theorem entire_at (row : Local C at_→Entry D K L) (f : Fin P→X→Option (Entry D K L))
    (measured : ∀p x,Gather.select R (host at_) p=some (loc x).1→f p x=localRaw C at_ raw row x) :
    collected at_ host loc R f=place (address C at_ host loc raw R near) row :=by
  rw [←entire C at_ host loc raw R near row (localRaw C at_ raw row) (fun _=>rfl)]
  funext j;let p:=finProdFinEquiv.symm j
  change (Gather.select R (host at_) p.1).bind (fun u=>oldAt loc (f p.1) u p.2)=(Gather.select R (host at_) p.1).bind _
  cases hit:Gather.select R (host at_) p.1 with
  | none=>rfl
  | some u=>
    change oldAt loc (f p.1) u p.2=oldAt loc (localRaw C at_ raw row) u p.2
    unfold oldAt;split
    · rename_i ok;apply measured;rw [ok.choose_spec];exact hit
    · rfl

/-- Use literally the first-grain old slot and `DescentRawCablePanel.role`
issued by the physical motif. `raw` simply forgets the two surviving
subtypes; its image proof requires positive donor width from the true span. -/
def ordinaryRaw {Y T : Type} (keep : Y→Prop) (trim : {y // keep y}→Prop) (mark : Y→T) (good : T→Prop)
    (positive : ∀e : {s : {y // keep y} // trim s},good (mark e.val.val)) :
    {s : {y // keep y} // trim s} ↪ {y // good (mark y)} where
  toFun e:=⟨e.val.val,positive e⟩
  inj' := fun _ _ eqn =>
    Subtype.ext (Subtype.ext (congrArg (fun y : {y // good (mark y)} => y.val) eqn))

end
end Hierarchy.DescentParallelBase.Resident

end OAI
