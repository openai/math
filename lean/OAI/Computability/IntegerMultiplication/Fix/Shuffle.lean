import OAI.Computability.IntegerMultiplication.Fix.Roster
import OAI.Computability.IntegerMultiplication.Code.Binary

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Code
variable {A B : Type}
def chief (x : Key) : Bool := x.headD false
def trunk (x : Key) : Key := x.tail
def blot (l : Store A) := l.map Prod.fst
def parcel (l : Store A) := l.map Prod.snd

-- operate on full or under keys.
variable [Codec A]
private def pick (b : Bool) (u : Key × A) :=
  bif decide (chief u.1=b) then [(trunk u.1,u.2)] else []
private theorem easy_chief : Easy chief := by
  have := Easy.listCase (X:=Bool) false (Easy.fst (X:=Bool) (Y:=Key))
  suffices h : chief = fun (l:Key) => List.casesOn (motive:=fun _=>Bool) l false (fun a _ => a) from h ▸ this
  ext l; cases l <;> rfl
private theorem easy_trunk : Easy trunk := by
  have := Easy.listCase (X:=Bool) ([]:Key) (Easy.snd (X:=Bool) (Y:=Key))
  suffices h : trunk = fun (l:Key) => List.casesOn (motive:=fun _=>Key) l [] (fun _ a => a) from h ▸ this
  ext l; cases l <;> rfl
private theorem easy_pick (b : Bool) : Easy (pick (A:=A) b) := by
  have c := Easy.fst (X:=Key) (Y:=A) |>.compose easy_chief
  have l := Easy.fst (X:=Key) (Y:=A) |>.compose easy_trunk
  have h := c.compose (Easy.finite (fun i => decide (i=b)))
  -- true branch construction
  unfold pick
  exact ((h.pair (l.pair Easy.snd)).compose (Easy.ifst (Easy.const _) (by fun_prop : Easy (fun x : Key × A => [x]))))

private def grab (b : Bool) (l : Store A) := (l.map (pick b)).flatten
private theorem easy_grab (b : Bool) : Easy (grab (A:=A) b) :=
  (easy_pick (A:=A) b |>.mapping).compose Easy.flatten
omit [Codec A] in
private theorem grabbed (a : Store A) (h : ∀ i∈a,i.1≠[]) (b : Bool) :
    grab b a=filter b a := by
  induction a with
  | nil => rfl
  | cons t a ih =>
    have e := h _ List.mem_cons_self
    specialize ih (fun i g => h _ (List.mem_cons_of_mem _ g))
    obtain ⟨_ | ⟨j,u⟩,t⟩ := t
    · contradiction
    by_cases z : j=b <;> simp [pick,trunk,chief,grab,filter,select,z,-List.map_map] at *
    all_goals assumption
omit [Codec A] in
private theorem active (k : ℕ) (h : 0<k) (l : Store A) (g : ∀ i∈l,i.1.length=k) :
    ∀ i∈l,i.1≠[] := by intro i e v; have := g i e; rw [v,List.length_nil] at this; omega

private def pairU (l : List Key) := l.map (fun v => (v,()))
private def inked (b : Bool) (l : List Key) := blot (grab b (pairU l))
omit [Codec A] in
private theorem stores (b:Bool) (a : Schedule A) (h : 0<a.height) :
    inked b (blot a.dest) = blot (a.child h b).dest := by
  rw [inked,Schedule.child]
  dsimp only
  have hf := active a.height h a.dest a.snug'
  unfold pairU blot
  generalize a.dest=l at hf ⊢
  induction l with
  | nil => rfl
  | cons i l ih =>
    have e := hf i List.mem_cons_self
    specialize ih (fun i g => hf _ (List.mem_cons_of_mem _ g))
    obtain ⟨_ | ⟨x,v⟩,y⟩ := i
    · contradiction
    by_cases u:x=b <;> simp [grab,pick,select,filter,trunk,chief,u,-List.map_map] at *
    all_goals assumption
private theorem easy_ink (b : Bool) : Easy (inked b) :=
  ((show Easy pairU from Easy.mapping (by fun_prop)).compose (easy_grab _)).compose Easy.fst.mapping

/- apply collected bins at holes -/
def joinbins (l : List Bool × List A × List A) :=
  (Ribbon.unite (Ribbon.dress false (l.1,l.2.1),Ribbon.dress true (l.1,l.2.2))).flatten

theorem easy_join_bins : Easy (joinbins (A:=A)) := by
  let x := fun l : List Bool × List A × List A => Ribbon.dress false (l.1,l.2.1)
  let y := fun l : List Bool × List A × List A => Ribbon.dress true (l.1,l.2.2)
  have hx : Easy x := ((Easy.fst.pair (Easy.snd.compose Easy.fst))).compose (Ribbon.easyDress _)
  have hy : Easy y := ((Easy.fst.pair (Easy.snd.compose Easy.snd))).compose (Ribbon.easyDress _)
  exact (Ribbon.easyUnite (hx.pair hy)).compose Easy.flatten

omit [Codec A] in
theorem join_plates (l : List (Bool × A)) :
    joinbins (l.map Prod.fst,Ribbon.read false l,Ribbon.read true l)=l.map Prod.snd := by
  rw [joinbins,Ribbon.frame,Ribbon.frame,Ribbon.combine]
  induction l with
  | nil => rfl
  | cons v l ih =>
    rcases v with ⟨_ | _,v⟩ <;>
      simp only [List.map_cons,List.flatten_cons,ih] <;>
      rfl

def question (s : Schedule A) := (s.src,blot s.dest)
def input (s : Schedule A) := send (question s)
def output (a : Schedule A) := send (parcel a.dest)
def road (v : List Key) := v.map chief
def side (a : Schedule A) := send (road (blot a.dest))

def prepareFlag (l : Store A) :=
  List.casesOn (motive:=fun _=>Bool) l false fun x _ =>
    List.casesOn (motive:=fun _=>Bool) x.1 false fun _ _ => true
private theorem look : Easy (prepareFlag (A:=A)) :=
  Easy.listCase _ (Easy.fst.compose (Easy.fst.compose (Easy.listCase _ (Easy.const _))))
private def prep (l : Store A × List Key) : Tree :=
  let next b := (grab b l.1,inked b l.2)
  send (prepareFlag l.1,(bif prepareFlag l.1 then
    send (next false,next true,road l.2)
    else send (parcel l.1)))
private theorem easy_prep : Easy (prep (A:=A)) := by
  let j b := fun l : Store A × List Key => (grab b l.1,inked b l.2)
  have h b : Easy (j b) := (Easy.fst.compose (easy_grab _)).pair (Easy.snd.compose (easy_ink b))
  have t : Easy (fun l : Store A × List Key => (j false l,j true l,road l.2)) :=
    (h _).pair ((h _).pair (Easy.snd.compose easy_chief.mapping))
  have f (p) [Codec p] : Easy (send (X:=p)) := Code.Task.self
  have a := Easy.fst (X:=Store A) (Y:=List Key) |>.compose look
  have x := Easy.fst (X:=Store A) (Y:=List Key) |>.compose (Easy.snd.mapping)
  exact (a.pair ((a.pair (x.compose (f _) |>.pair (t.compose (f _)))).compose (Easy.ifst Easy.fst Easy.snd))).compose (f _)
-- branch twins
open Code.Tunnel
def branch (a : Schedule A) : Option (Schedule A × Schedule A) :=
  if h : 0<a.height then (bif a.src.isEmpty then Option.none else some (a.child h false,a.child h true)) else .none
theorem made (a : Schedule A) :
    prep (question a)=crest branch input output side a := by
  by_cases e:a.src=[]
  · have h := a.miss e
    simp [question,output,parcel,prep,prepareFlag,crest,wing,branch,e,h] -- dif; split
    exact ⟨rfl,rfl⟩
  obtain ⟨x,l,z⟩ : ∃ x l,a.src=x::l := List.exists_cons_of_ne_nil e
  have h := a.snug x (z ▸ List.mem_cons_self)
  unfold prep question
  by_cases d0 : 0<a.height
  · obtain ⟨b,t,h'⟩ : ∃ b t,x.1=b::t := by
      cases e:x.1
      · simp [e] at h; omega
      · exact ⟨_,_,rfl⟩ -- e rw case?
    have p : prepareFlag a.src=true := by rw [z,prepareFlag]; simp only [h']
    rw [p]
    have pf (v:Bool) := grabbed a.src (active _ d0 _ a.snug) v
    have em : List.isEmpty a.src=false := by rw [z]; rfl
    change Tree.fork (send true) (send (send (_,_,_))) = _
    have pp (b:Bool) := stores b a d0
    simp only [crest,wing,branch,dite_eq_left d0,em,Bool.cond_false,Option.isSome_some,pp,pf]
    rfl
  have p : x.1=[] := by rw [← List.length_eq_zero_iff,h]; omega
  have g : prepareFlag a.src=false := by rw [z, prepareFlag]; simp [p]
  rw [g]
  simp [crest,wing,branch,d0,output,parcel,a.shallow (by omega)]
  exact ⟨rfl,rfl⟩

theorem helps :
    Task (fun a:Schedule A => size (question a)) input (crest branch input output side) := by
  have h := Task.on (easy_prep (A:=A)) question
  exact h.conform (fun _ => rfl) (fun _ => rfl) (fun i => by change prep _ = _; rw [made])

omit [Codec A] in
theorem restored (v : Twins (branch (A:=A))) :
    joinbins (road (blot v.main.dest), parcel v.x.dest,parcel v.y.dest)=parcel v.main.dest := by
  obtain ⟨a,x,y,h⟩ := v
  unfold branch at h
  split at h
  next i =>
    by_cases e : a.src.isEmpty
    · simp [e] at h
    simp [e] at h
    obtain ⟨rfl,rfl⟩ := h
    -- bins
    have d := join_plates (a.dest.map Schedule.hats)
    simp only [List.map_map] at d
    simpa only [Schedule.hats, Function.comp_def,chief,parcel,road,blot,List.map_map,← a.scattered i false,
      ← a.scattered i true] using d
  contradiction

end Fix

end IntegerMultiplication
end Computability
end OAI
