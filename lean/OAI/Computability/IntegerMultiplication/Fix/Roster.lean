import OAI.Computability.IntegerMultiplication.Code.Filter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Code
abbrev Key := List Bool
abbrev Store (A : Type) := List (Key × A)

variable {A B : Type}
def leaf {Y : Type} [DecidableEq Y] (y : Y) (i : Y × A) :=
  if i.1=y then [i.2] else []
def draw (y : Key) (l : Store A) := l.flatMap (leaf y)
def select (b : Bool) (x : Key × A) : Store A :=
  x.1.casesOn [] fun c t => if c=b then [(t,x.2)] else []
def filter (b : Bool) (x : Store A) := x.flatMap (select b)

theorem read_filter (b : Bool) (l : Store A) (t : Key) :
    draw t (filter b l)=draw (b::t) l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨_ | ⟨f,h⟩,a⟩ := q
    · simpa [draw,leaf,select,filter] using ih
    by_cases e : f=b <;> by_cases g : h=t <;>
      simpa [draw,filter,leaf,select,e,g] using ih

theorem less_length (b : Bool) (l : Store A) (k : ℕ)
    (h : ∀ i∈l,i.1.length=k+1) :
    ∀ i ∈ filter b l,i.1.length=k := by
  rintro ⟨i,f⟩ d
  obtain ⟨⟨_|⟨a,j⟩,x⟩,y,e⟩ := List.mem_flatMap.mp d <;> simp [select] at e
  have z := h _ y
  simp at *
  obtain ⟨rfl,rfl,rfl⟩ := e
  exact z

structure Schedule (A : Type) where
  height : ℕ
  src : Store A
  dest : Store A
  snug : ∀i∈src,i.1.length=height
  snug' : ∀i∈dest,i.1.length=height
  route i : draw i src = draw i dest

namespace Schedule
-- recurse children even when no data but keys lengths. handle height=0 OR src<> nonempty.
def child (a : Schedule A) (h : 0<a.height) (b : Bool) : Schedule A where
  height := a.height-1
  src := filter b a.src
  dest := filter b a.dest
  snug := less_length _ _ _ (fun i v => by rw [a.snug i v]; omega)
  snug' := less_length _ _ _ (fun i v => by rw [a.snug' i v]; omega)
  route i := by simp only [read_filter,a.route]

def empty (s : Schedule A) := s.src=[]
theorem miss (s : Schedule A) (h : empty s) : s.dest=[] := by
  by_contra q
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ q -- lemma
  have d := s.route x.1
  unfold draw at d
  rw [show s.src=[] from h] at d
  have : x.2∈s.dest.flatMap (leaf x.1) := List.mem_flatMap.mpr ⟨x,hx,by simp [leaf]⟩
  simp [← d] at this

theorem shallow (s : Schedule A) (h : s.height=0) :
    s.src.map Prod.snd=s.dest.map Prod.snd := by
  have d (l : Store A) (e : ∀i : Key × A, i∈l → i.1.length=0) : l.map Prod.snd= draw [] l := by
    induction l with
    | nil => rfl
    | cons x l ih =>
      specialize ih (fun _ h => e _ (List.mem_cons_of_mem _ h))
      have y := e _ List.mem_cons_self
      simp only [List.length_eq_zero_iff] at y
      simp [draw, leaf,y] at *
      exact ih
  rw [d _ (fun _ e => h ▸ s.snug _ e), d _ (fun _ e => h ▸ s.snug' _ e), s.route]

def hats (x : Key × A) : Bool × A :=
  (x.1.headD false,x.2)
theorem scattered (a : Schedule A) (e : 0<a.height) (b : Bool) :
    Ribbon.read b (a.dest.map hats) = (a.child e b).dest.map Prod.snd := by
  unfold child
  suffices h : ∀ l:Store A,(∀ i∈l,i.1.length=a.height) →
      Ribbon.read b (l.map hats) = (filter b l).map Prod.snd by exact h _ a.snug'
  intro l h
  induction l with
  | nil => rfl
  | cons q l ih =>
    specialize ih (fun i t => h _ (List.mem_cons_of_mem _ t))
    have : q.1≠[] := by have := h q List.mem_cons_self; intro t; rw [t,List.length_nil] at this; omega
    obtain ⟨_ | ⟨v,t⟩,x⟩ := q
    · contradiction
    by_cases g : v=b <;>
      simp only [filter,Ribbon.read] at * <;>
      simp [Ribbon.keep,hats,select,g,ih,-List.map_map]

end Schedule
end Fix

end IntegerMultiplication
end Computability
end OAI
