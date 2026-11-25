import OAI.Computability.IntegerMultiplication.Code.Chunk

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
namespace Ribbon
variable {A B : Type*} [Codec A] [Codec B] [DecidableEq A] [FiniteState A]

/-- get one stream by keys already in left components -/
def keep (a : A) (i : A × B) : List B :=
  bif decide (i.1=a) then [i.2] else []
def read (a : A) (l : List (A×B)) :=
  (l.map (keep a)).flatten

@[fun_prop] theorem easyKeep (a : A) {I : Type*} [Codec I] {v : I → A × B} (h : Easy v) :
    Easy (fun i => keep a (v i)) := by
  have u := h.fstCompose.compose (Easy.finite (fun k => decide (k=a)))
  exact (u.pair h).compose (Easy.ifst (Easy.const _) (by fun_prop : Easy (fun i : A×B => [i.2])))

@[fun_prop] theorem easyRead (a : A) {I : Type*} [Codec I] {v : I→List (A×B)} (h : Easy v) :
    Easy (fun i => read a (v i)) := by unfold read; fun_prop

def width (a : A) (l : List A) := List.map (fun b => if b=a then [()] else []) l
def dress (a : A) (i : List A × List B) :=
  (Piecework.segment (width a i.1) i.2).1

theorem easyDress (a : A) : Easy (dress (B:=B) a) := by
  have e : Easy (fun b => if b=a then [()] else []) := Easy.finite _
  unfold dress width
  fun_prop

omit [Codec A] [Codec B] [FiniteState A] in
theorem frame (a : A) (l : List (A×B)) :
    dress a (l.map Prod.fst,read a l) = l.map (keep a) := by
  unfold dress read width
  have K : ((fun b => if b=a then [()] else []) ∘ (Prod.fst : A × B → A)) =
      (tally ∘ List.length ∘ keep a) := by
    funext x; unfold keep; by_cases e : x.1=a <;> simp [Function.comp_def,e,tally,List.replicate_succ]
  rw [List.map_map,K,
      show List.map (tally ∘ List.length ∘ keep a) l =
        (l.map (keep a)).map (tally ∘ List.length) by simp [Function.comp_def],
      Piecework.prescribed]

-- combine partial list columns pointwise
def gather (i : List (List B) × List (List B)) :=
  List.map (fun p => p.1 ++ p.2) (zipSafe [] [] i)
-- zipSafe includes extra empty tail; adjust by taking ruler of first list
def unite (i : List (List B) × List (List B)) :=
  (cutLists (ruler i.1,gather i)).1

@[fun_prop] theorem easyUnite {I : Type*} [Codec I] {f : I→List (List B) × List (List B)} (u : Easy f) :
    Easy (fun i => unite (f i)) := by
  let x := fun i => (ruler (f i).1,gather (f i))
  have h : Easy x := ((Easy.ruler u.fstCompose).pair (by unfold gather; fun_prop)) -- name
  exact (easy_cut h).fstCompose

omit [Codec B] in
theorem combine {X : Type*} (l : List X) (f g : X→List B) :
    unite (l.map f,l.map g) = l.map (fun a => f a ++ g a) := by
  apply List.ext_getElem
  · simp [unite,gather,cutLists,ruler_length,zipSafe]
  intro i hi he
  have e : i<l.length := by simpa using he
  simp [unite,gather,cutLists,ruler_length,zipSafe,e, List.getElem_append_left]

def collect (l : List A) (v : A × B) := if v.1∈l then [v.2] else []

omit [Codec A] [FiniteState A] in
omit [Codec B] in
theorem collecting (q : List (A × B)) (a : A) (l : List A) (h : a∉l) :
    unite (q.map (keep a),q.map (collect l)) = q.map (collect (a::l)) := by
  rw [combine]
  refine List.map_inj_left.mpr ?_
  intro k _
  by_cases e : k.1=a
  · simp [e,keep,collect,h]
  by_cases g : k.1∈l <;> simp [keep,e,collect,g]

-- aggregation generic family
variable {I : Type*}
-- easier Carries forms separate module; prove Computes compatible via length; use fun_prop closures const.
theorem emulate (cats : List A) (key : I → List A) (payload : A → I→List B)
    [Codec I]
    (hu : Easy key) (hw : ∀ a∈cats, Easy (payload a)) :
    Easy (fun i => (cats.foldr (fun b l => unite (dress b (key i,payload b i),l))
      ((key i).map (fun _ => []))) ) := by
  induction cats with
  | nil => dsimp only [List.foldr_nil]; fun_prop
  | cons a l ih =>
    dsimp only [List.foldr_cons]
    apply easyUnite
    specialize ih (fun b hb => hw b (List.mem_cons_of_mem _ hb))
    exact (((hu.pair (hw a List.mem_cons_self)).compose (easyDress a)).pair ih)

end Ribbon
end Code

end IntegerMultiplication
end Computability
end OAI
