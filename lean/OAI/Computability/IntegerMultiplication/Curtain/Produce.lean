import OAI.Computability.IntegerMultiplication.Curtain.Scanner
import OAI.Computability.IntegerMultiplication.Curtain.Choice

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
variable {L:ℕ} (g: Fin L→ Fin L) (e : ∀ x,g (g x)=x)

def rest (d : Bool) := (List.ofFn id).filter (fun x => bif d then decide (x = g x) else decide (x < g x))
theorem rest_m (d) (x : Fin L) : x∈rest g d ↔ bif d then x=g x else x < g x := by
  cases d <;> simp [rest]
theorem rest_n d : List.Nodup (rest g d) := by
  apply List.Nodup.filter
  -- unknown
  exact List.nodup_ofFn.mpr (show Function.Injective (id : Fin L→Fin L) from fun _ _ h=>h)
abbrev run (d) := (rest g d).length

section
variable {A : Type}
-- provide bounded cast list equival to elements for arbitrary injective list
def sense (l : List A) (p : l.Nodup) : Fin l.length ↪ A where
  toFun i := l.get i
  inj' := fun _ _ => List.Nodup.get_inj_iff p |>.1 -- binder?
theorem listens (l : List A) (p : l.Nodup) (i:Fin l.length) : sense l p i ∈ l := List.get_mem ..
theorem temps {l : List A} (p : l.Nodup) {x : A} (v : x ∈ l) : ∃ i, sense l p i=x :=
  List.mem_iff_get.mp v
theorem mkL (l : List A) (p : l.Nodup) : List.ofFn (sense l p)=l := List.ofFn_get l
end

abbrev here (d) := sense (rest g d) (rest_n g d)
theorem here_f (i) : here g true i=g (here g true i) :=
  (rest_m g true _).1 (listens ..)
theorem here_l (i) : here g false i < g (here g false i) :=
  (rest_m g false _).1 (listens ..)

open Net Net.Walsh
abbrev Rol := Fin (run g true) ⊕ Fin (run g false) × B
def rolled (t : Rol g) : Fin L :=
  Sum.elim (here g true) (fun u=> if u.2=0 then here g false u.1 else g (here g false u.1)) t

theorem rs (i) : rolled g (.inr (i,0))=here g false i := by change (if (0:B)=0 then here g false i else g (here g false i)) = _; exact ite_eq_left (show (0:B)=0 from rfl)
theorem rb (i) : rolled g (.inr (i,1))=g (here g false i) := by change (if (1:B)=0 then here g false i else g (here g false i)) = _; exact ite_eq_right (show (1:B)≠0 by decide)
include e
theorem covered (x : Fin L) : ∃ i,rolled g i=x := by
  rcases lt_trichotomy x (g x) with h|h|h
  · obtain ⟨i,c⟩ := temps (rest_n g false) ((rest_m g false x).2 h)
    exact ⟨.inr (i,0),(rs g _).trans c⟩
  · obtain ⟨i,c⟩ := temps (rest_n g true) ((rest_m g true x).2 h)
    exact ⟨.inl i,c⟩
  obtain ⟨i,c⟩ := temps (rest_n g false) ((rest_m g false (g x)).2 (show g x < g (g x) by rw [e]; exact h))
  exact ⟨.inr (i,1),(rb g i).trans ((congrArg g c).trans (e _))⟩

private theorem biface (i j) : rolled g (.inl i) ≠ rolled g (.inr j) := by
  have q := here_f g i
  rcases j with ⟨j,b⟩
  have f := here_l g j
  intro h
  rcases bit_value b with d|d
  · subst b
    rw [rs,show rolled g (.inl i)=here g true i from rfl] at h
    rw [h] at q
    exact f.ne q
  subst b
  rw [rb,show rolled g (.inl i)=here g true i from rfl] at h
  rw [h,e] at q; exact f.ne' q

private theorem bridge (i j) : rolled g (.inr (i,0))≠ rolled g (.inr (j,1)) := by
  intro h
  rw [rb,rs] at h
  have u := here_l g i
  rw [h,e] at u
  exact (not_lt_of_gt (here_l g j)) u

theorem directR : Function.Injective (rolled g) := by
  rintro (i|⟨i,s⟩) (j|⟨j,t⟩) u
  · exact congrArg _ ((here g true).injective u)
  · exact (biface g e i _ u).elim
  · exact (biface g e j _ u.symm).elim
  rcases bit_value s with s'|s' <;> rcases bit_value t with t'|t' <;> subst s <;> subst t
  · exact congrArg (fun i=> Sum.inr (i,0)) ((here g false).injective u)
  · exact (bridge g e i j u).elim
  · exact (bridge g e j i u.symm).elim
  have h := congrArg g u
  rw [rb,rb,e,e] at h
  exact congrArg (fun i=> Sum.inr (i,1)) ((here g false).injective h)

noncomputable def coal : Attach L (run g true) (run g false) := Equiv.ofBijective (rolled g) ⟨directR g e,covered g e⟩
theorem produces (x:Fin L) :
    Pin.pos (coal g e) x=g x := by
  obtain ⟨x,rfl⟩ := (coal g e).surjective x
  rcases x with x|⟨i,v⟩
  · exact (Pin.still ..).trans (here_f g x)
  rcases bit_value v with u|u <;> subst v <;> rw [Pin.spill]
  · rw [zero_add]; exact (rb ..).trans (congrArg g (rs g i).symm)
  rw [show (1:B)+1=0 by decide]
  change rolled g (.inr (i,0))=g (rolled g (.inr (i,1)))
  rw [rb,rs,e]

omit e
theorem noMore (d) : run g d≤L := by
  apply le_trans (b:=(List.ofFn (id (α:=Fin L))).length) (List.length_filter_le ..) List.length_ofFn.le

open Code Code.Iter
-- compile reports by list filter+map
def title (s : Bool) (x : Roll×Count) :=
  bif s then decide (x.2.length=(star x).length) else decide (x.2.length<(star x).length)
@[fun_prop] theorem poly_t (d) : Poly (title d) := by
  unfold title
  cases d
  · exact (Easy.snd.poly.pair pyS).compose (small_easy.poly)
  exact (Easy.snd.poly.pair pyS).compose (linked.poly)
def playbill (v:Roll×Bool) :=
  (polyPush (fun x=>
    bif title v.2 x then [x.2] else []) (v.1,lineup (ruler v.1))).flatten
-- fix v.2
theorem bills (d) : Poly (fun v:Roll=> playbill (v,d)) := by
  unfold playbill
  have a := Poly.push ([]:Roll) ([]:Count)
    (show Poly (fun x:Roll×Count=> bif title d x then [x.2] else []) by have u:=poly_t d; fun_prop)
  have h : Poly (fun v:Roll=> lineup (ruler v)) := (Easy.ruler Easy.identity).poly.compose poly_line
  exact (((Poly.identity.pair h).compose a).compose Easy.flatten.poly)
theorem printed (d) :
    playbill (paint g,d) = (rest g d).map (fun x=> tally x.val) := by
  unfold playbill polyPush
  change (((lineup (ruler (paint g))).map _).flatten)=_
  rw [show lineup (ruler (paint g))=List.ofFn (fun i:Fin L=> tally i.val) from by
    simp [lineup,paint,ruler]
    funext i
    rfl]
  -- direct identity
  unfold rest
  suffices e : ∀ l : List (Fin L),
      ((l.map (fun i:Fin L=> tally i.val)).map (fun y=> bif title d (paint g,y) then [y] else [])).flatten =
      ((l.filter (fun x=> bif d then decide (x=g x) else decide (x<g x))).map (fun i=>tally i.val)) by
    have r := e (List.ofFn (id (α:=Fin L)))
    simp only [List.map_ofFn,Function.comp_id] at r
    simpa using r
  intro l; induction l with
  | nil=>rfl
  | cons i l ih=>
    have T : title d (paint g,tally i.val) = (bif d then decide (i=g i) else decide (i<g i)) := by
      simp [title,star,entry,paint,tally_length]
      cases d <;> simp [Fin.ext_iff]
    rw [List.map_cons,List.map_cons,T]
    cases v : bif d then decide (i=g i) else decide (i<g i)
    · change ((l.map (fun i:Fin L=> tally i.val)).map
        (fun y=> bif title d (paint g,y) then [y] else [])).flatten = _
      cases d <;> simp_all
    · change tally i.val :: ((l.map (fun i:Fin L=> tally i.val)).map
        (fun y=> bif title d (paint g,y) then [y] else [])).flatten = _
      cases d
      · have hv : i < g i := by simpa using v
        simpa [List.filter_cons, hv] using congrArg (List.cons (tally i.val)) ih
      · simpa only [List.filter_cons, ite_eq_left v, List.map_cons] using
          congrArg (List.cons (tally i.val)) ih

def billrun (s : Roll) : Report :=
  (playbill (s,true), polyPush (fun x=> (x.2,star x)) (s,playbill (s,false)))
@[fun_prop] theorem poly_run : Poly billrun := by
  unfold billrun
  have r := Poly.push ([]:Roll) ([]:Count) (Easy.snd.poly.pair pyS)
  have j : Poly (fun s:Roll=>playbill (s,false)) := bills _
  have d : Poly (fun s:Roll=>playbill (s,true)) := bills _
  fun_prop
include e
theorem bill_s :
    billrun (paint g)= report (coal g e) := by
  unfold billrun report polyPush
  simp only [printed,List.map_map,Function.comp_def]
  simp_rw [star,entry]
  change (_,List.map _ _)=
    (List.ofFn (fun i=>tally (here g true i).val),List.ofFn (fun i=> (tally (rolled g (.inr (i,0))).val,tally (rolled g (.inr (i,1))).val)))
  simp_rw [rb,rs]
  have r {A} (d:Bool) (f : Fin L→A) : (rest g d).map f=List.ofFn (fun i=> f (here g d i)) := by
    change _=List.ofFn (f ∘ (here g d))
    rw [← List.map_ofFn]
    rw [mkL]
  rw [r,r]
end Curtain

end IntegerMultiplication
end Computability
end OAI
