import OAI.Computability.IntegerMultiplication.Code.Auto
import OAI.Computability.IntegerMultiplication.Code.Zip

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {X Y Z : Type*}

/-- View any list as a unary ruler (ignore item values). -/
abbrev Tally := List Unit
def tally (n : ℕ) : Tally := List.replicate n ()

@[simp] theorem tally_length (n) : (tally n).length=n := by simp [tally]
@[simp] theorem tally_succ (n) : tally (n+1)=()::tally n := by simp [tally,List.replicate_succ]
theorem size_tally (l : Tally) : size l = 2*l.length+1 := by
  induction l with
  | nil => rfl
  | cons h l ih => simp [show size h=1 from rfl,ih]; omega

def ruler (x : List X) : Tally := List.map (fun _ => ()) x
@[simp] theorem ruler_length (x : List X) : (ruler x).length=x.length := by simp [ruler]

variable [Codec X]

@[fun_prop] theorem Easy.ruler {g : Z→List X} [Codec Z] (h : Easy g) :
    Easy (fun x => ruler (g x)) := by unfold IntegerMultiplication.Code.ruler; fun_prop

private def cutBody : Cmd :=
  -- ruler on 1, list on 0, outputs prefix :suffix (NO pair tag yet) on 0.
  splitRoot 1
    (fun _ => give 0 false)
    (splitRoot 1 (fun _ =>
      splitRoot 0
        (fun _ => .join (discard 1)
          (.join (give 0 false) (give 0 false)))
        (.join (move 0 3 2)
          (.join (.again 0) (.join (move 3 0 2) (pack 0)))))
      .pass)

def cutLists (i : Tally × List X) : List X × List X :=
  (i.2.take i.1.length, i.2.drop i.1.length)

/-- Split off a prefix in linear time in requested plus consumed size. There is no
charge for processing any elements or visiting the data beyond that prefix. -/
theorem Computes.cut :
    Computes (fun i : Tally × List X => size i.1+size (cutLists i).1) cutLists := by
  let b := cutBody
  refine ⟨splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((Prog.tie b).join (pack 0))), 160,fun i env r => ?_⟩
  rcases i with ⟨c,l⟩
  suffices he : ∀ (c : Tally) (l : List X) r, Fits (b::env) b
      (pile 1 (send c) (pile 0 (send l) r))
      (pile 0 (send (cutLists (c,l)).1) (pile 0 (send (cutLists (c,l)).2) r))
      (110*(size c+size (cutLists (c,l)).1)) by
    refine (fits_pair ((fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide)
      _ env _).join ((he c l r).tie.join (fits_pack _ _ _ _ _)))).mono ?_
    change 42*size c+_+_+_ ≤ 160*(size c+size (cutLists (c,l)).1+1)
    omega
  intro c' l' r'
  let G := b::env
  induction c' generalizing l' r' with
  | nil =>
    simp only [cutLists,List.length_nil,List.take_zero,List.drop_zero]
    exact (fits_bit (c:=fun _ => give 0 false) (b:=false) (fits_give false _ _ _)).mono (by simp)
  | cons x c ih =>
    cases l' with
    | nil =>
      simp only [cutLists,List.length_cons,List.take_nil,List.drop_nil]
      have h₁ := (fits_discard 1 (send c) G r').join ((fits_give false r' 0 G).join (fits_give false _ 0 G))
      have h := fits_bit (i:=0) (b:=false) (c:= fun _ => _) (d := Prog.join (move 0 3 2) (.join (.again 0) (.join (move 3 0 2) (pack 0)))) h₁ -- unresolved inner
      -- reorder nil for second arm of splitroot on stack1 (its input ruler tail above nil).
      rw [pile_comm 0 _ r' 1 _ (by decide)] at h
      refine (fits_pair (fits_bit (b:=false) (c:= fun _ => _) (d:=Prog.pass) h)).mono ?_
      change 17*size c+_+_+_+_+_ ≤ _
      simp only [size_cons]
      omega
    | cons a l =>
      simp only [cutLists,List.length_cons,List.take_succ_cons,List.drop_succ_cons]
      have h₁ := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) (send a) G
        (pile 1 (send c) (pile 0 (send l) r'))
      rw [pile_comm 3 _ _ 1 _ (by decide), pile_comm 3 (send a) r' 0 _ (by decide)] at h₁ -- stack0 crossing for input?
      have hi := ih l (pile 3 (send a) r')
      have h₂ := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) (send a) G
        (pile 0 (send (cutLists (c,l)).1) (pile 0 (send (cutLists (c,l)).2) r'))
      rw [pile_comm 3 _ _ 0 _ (by decide), pile_comm 3 _ _ 0 _ (by decide)] at h₂
      have hh := h₁.join ((Fits.again0 hi).join (h₂.join (fits_pack (send a) _ _ 0 _)))
      rw [pile_comm 1 (send c) r' 0 (send l) (by decide)] at hh
      have hx := fits_pair (c:= fun _ => (Prog.join (discard 1) (.join (give 0 false) (give 0 false)))) hh
      rw [pile_comm 0 (.fork ..) _ 1 _ (by decide)] at hx
      refine (fits_pair (fits_bit (b:=false) (c:= fun _ => _) (d:=Prog.pass) hx)).mono ?_
      simp only [size_cons,cutLists]
      change 42*size a+ (_ +1+ (42*size a+1+2)+2)+2+4+4+4≤ _
      omega

@[fun_prop] theorem easy_cut [Codec Z] {g : Z → Tally × List X} (h : Easy g) :
    Easy (fun x => cutLists (g x)) := by
  apply h.compose
  apply Easy.of_bound (Computes.cut (X:=X)) 1
  intro i
  rcases i with ⟨k,l⟩
  have he : size (l.take k.length) ≤ size l := by
    have e := size_append_right (l.take k.length) (l.drop k.length)
    rw [List.take_append_drop] at e
    have h := size_pos (l.drop k.length)
    omega
  simp only [size_prod,cutLists]
  omega

/-- pad both lists to a common length, then zip them. c and d are fixed, not supplied.
This traverses inputs and does not require or promise matched original lengths. -/
def zipSafe (c : X) (d : Y) (p : List X × List Y) : List (X × Y) :=
  (p.1 ++ List.replicate p.2.length c).zip (p.2 ++ List.replicate p.1.length d)

def fill (x : X) : Tally → List X := List.map fun _ => x

@[fun_prop]
theorem easy_fill [Codec Z] (c : X) {g : Z → Tally} (h : Easy g) :
    Easy (fun i => fill c (g i)) := by unfold fill; fun_prop

omit [Codec X] in
theorem fill_eq (c : X) (s : Tally) : fill c s=List.replicate s.length c := by
  induction s <;> simp_all [fill,List.replicate_succ]

-- as intermediate, restrictive case where lengths match.
variable [Codec Y]
theorem zip_spec :
    Task (fun x : {i : List X × List Y // i.1.length=i.2.length} => size x.val)
      (fun i => send i.val)
      (fun i => send (i.val.1.zip i.val.2)) := by
  let V := {i : List X × List Y // i.1.length=i.2.length}
  have hw := (Task.zipTrees (fun i : X × Y => send i.1) (fun i => send i.2)).on (fun x : V => x.val.1.zip x.val.2)
  have he (x : V) :
      Task.forest (fun i : X × Y => send i.1) (x.val.1.zip x.val.2) = send x.val.1 ∧
      Task.forest (fun i : X × Y => send i.2) (x.val.1.zip x.val.2) = send x.val.2 := by
    rcases x with ⟨⟨l,s⟩,h⟩
    dsimp at *
    rw [← Task.forest_map send Prod.fst, ← Task.forest_map send Prod.snd]
    have hu : l.length=s.length := h
    simp [List.map_fst_zip,List.map_snd_zip,hu]
  refine (Task.conform (b':=fun x => size x.val.1 + size x.val.2) hw (fun x => ?_) (fun x => ?_) (fun x => ?_)).mono (fun x => by simp)
  · simp only [(he x).1,(he x).2,size]
  · simp only [(he x).1,(he x).2,send_prod]
  · have h : send (X:=X × Y)=(fun i => Tree.fork (send i.1) (send i.2)) := rfl
    rw [← h,Task.forest_send]

theorem Easy.zipSafe (c : X) (d : Y) : Easy (zipSafe c d) := by
  let p (i : List X × List Y) := (i.1++List.replicate i.2.length c, i.2++List.replicate i.1.length d)
  have h : Easy p := by
    have e : p=(fun i : List X × List Y => (i.1++fill c (IntegerMultiplication.Code.ruler i.2),i.2++fill d (IntegerMultiplication.Code.ruler i.1))) :=
      funext (by intro i; simp [p,fill_eq])
    rw [e]
    fun_prop
  obtain ⟨C,hc⟩ := h.length
  refine Easy.of_bound (Task.compose (p:=send) h (zip_spec.on (fun i => ⟨p i,by simp [p,add_comm]⟩))) (C+1) ?_
  intro i
  dsimp only
  specialize hc i
  rw [Nat.add_mul,Nat.one_mul]
  omega

@[fun_prop]
theorem easy_zipSafe (c : X) (d : Y) [Codec Z] {g : Z → List X × List Y} (h : Easy g) :
    Easy (fun x => zipSafe c d (g x)) := h.compose (Easy.zipSafe _ _)

end Code

end IntegerMultiplication
end Computability
end OAI
