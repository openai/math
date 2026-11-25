import OAI.Computability.IntegerMultiplication.Dune.Site

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dune
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau Atoll Wave
variable {X:Type}[Codec X]
def release_ (u:X)(g:List Bool × List X):List X :=
  Ribbon.read true (zipFair false u g)
@[fun_prop] theorem releaseE (u:X): Easy (release_ u):=
  (easy_zip ..).compose (Ribbon.easyRead true easy_id)
def collect (x: List X × X):X:= x.1.headD x.2
@[fun_prop] theorem collectE :Easy (collect (X:=X)) := by
  -- default variable x.2. list test via case line
  let f (q:List X × X):= (q.1++[q.2])
  have t : Nonempty X ∨ IsEmpty X := Classical.em _
    |>.imp (fun t => t) (fun v=> not_nonempty_iff.mp v)
  rcases t with T|v
  -- a Nonempty
  -- force choose
  · let a:X:=Classical.choice T
    have Q:=Iter.leader a (X:=X)
    have U:collect = (fun i:List X×X=> (f i).headD a):=by
      funext q; rcases q with ⟨_|⟨a,l⟩,b⟩ <;> rfl
    rw [U]
    exact Easy.compose (by unfold f; fun_prop) Q
  · suffices e:collect (X:=X)=Prod.snd from e ▸ Easy.snd
    funext k; exact (v.false k.2).elim
def gather_ (a:X)(x: List Bool × List X × List X):List X :=
  lock collect [] a (Ribbon.dress true (x.1,x.2.1),x.2.2)
@[fun_prop] theorem gatherE (a:X):Easy (gather_ a) :=
  (((Easy.fst.pair Easy.snd.fstCompose).compose (Ribbon.easyDress _)).pair Easy.snd.sndCompose).compose
    (easy_lock _ collectE ..)

variable {Y:Type}(s:Series Y)(l:Y→Bool)(x:Y→X)
omit [Codec X] in
theorem moment :
    Ribbon.read true (s.tab (fun a=>(l a,x a)))=(s.explore.filter l).map x := by
  unfold Series.tab Ribbon.read
  induction s.explore with
  | nil => rfl
  | cons a g ih=>
    simp only [List.map_cons,List.flatten_cons,List.filter]
    cases e:l a <;> simpa [Ribbon.keep,e] using ih
omit [Codec X] in
theorem releaseV (a):
    release_ a (s.tab l,s.tab x)=(s.explore.filter l).map x := by
  change Ribbon.read true (zipFair _ _ (s.explore.map _,s.explore.map _))=_
  rw [fair]; exact moment s l x
variable (y:Y→X)
omit [Codec X] in
theorem gatherV (a:X)(h:∀ i,l i=false→y i=x i):
    gather_ a (s.tab l,(s.explore.filter l).map x,s.tab y)=s.tab x := by
  let v:=s.tab fun i=>(l i,x i)
  have q : (s.tab (fun i=>(l i,x i))).map Prod.fst = s.tab l:=by rw [Series.map_tab];rfl
  unfold gather_; change lock _ _ _ (Ribbon.dress _ (s.tab l, _),_)=_
  rw [← moment,← q]
  rw [Ribbon.frame,Series.map_tab,paired]
  apply congrArg (s.tab)
  funext i
  cases e:l i <;> simp [Ribbon.keep,e,collect,h i]
end Dune

end IntegerMultiplication
end Computability
end OAI
