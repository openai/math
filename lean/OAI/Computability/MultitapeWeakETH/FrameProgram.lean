import OAI.Computability.MultitapeWeakETH.RankProgram
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding

/-! # A polynomial-time tape reader for nested binary frames -/

namespace OAI.Computability.MultitapeWeakETH.FrameProgram

open IntegerMultiplication Code Algorithms.SubexponentialSAT Encoding

abbrev Word := List Bool
private abbrev State := (Bool × Bool) × List Word × Word × Word

/-- The finite flags record a list tag, frame tag, escaped bit, or the
suffix following the list terminator. A missing terminator rejects. -/
private def step (p : State × Bool) : State :=
  let s := p.1
  let b := p.2
  let records := s.2.1
  let current := s.2.2.1
  let tail := s.2.2.2
  bif s.1.1 then
    bif s.1.2 then ((true,false),records,current++[b],tail)
    else bif b then ((true,true),records,current,tail) else ((false,false),records++[current],[],tail)
  else bif s.1.2 then ((false,true),records,current,tail++[b])
    else bif b then ((true,false),records,current,tail) else ((false,true),records,current,tail)

private def walk (bits : Word) (s : State) := bits.foldl (fun z b => step (z,b)) s

private theorem step_poly : Poly step := by unfold step; fun_prop

private theorem step_size (s : State) (b : Bool) : size (step (s,b)) ≤ size s+4 := by
  rcases s with ⟨⟨v,f⟩,rs,cur,tail⟩
  have snoc {X : Type} [Codec X] (l : List X) (z : X) : size (l++[z]) = size l+size z+1 := by
    have h := size_append_right l [z]
    simp only [size_cons,size_nil] at h
    omega
  have v₀ : size false=1 := rfl
  have v₁ : size true=1 := rfl
  cases v <;> cases f <;> cases b <;> simp [step,snoc,v₀,v₁] <;> omega

private theorem walk_poly : Poly (fun p : Word × State => walk p.1 p.2) := by
  apply Poly.fold_left step_poly 5 1
  rintro ⟨xs,s⟩ l h
  have cost (bs : Word) (st : State) : size (walk bs st) ≤ size st+4*bs.length := by
    induction bs generalizing st with
    | nil => simp [walk]
    | cons b bs ih =>
      change size (walk bs (step (st,b))) ≤ _
      have := ih (step (st,b))
      have := step_size st b
      simp only [List.length_cons]; omega
  have a := cost l s
  have b := h.length_le
  have c := duration xs
  change l.length ≤ xs.length at b
  change size (walk l s) ≤ 5*(size xs+size s+1+1)^1
  rw [pow_one]
  exact a.trans (by omega)

private def base : State := ((false,false),[],[],[])

/-- The Boolean field records whether the list terminated. The returned
suffix makes the same routine usable on an encoded clause or a padded
descriptor path. -/
def read (bits : Word) : Bool × List Word × Word :=
  let s := walk bits base
  ((!s.1.1 && s.1.2),s.2.1,s.2.2.2)

theorem read_poly : Poly read := by
  have init := (Poly.identity (X:=Word)).pair (Easy.const (X:=Word) base).poly
  have get : Poly (fun s : State => ((!s.1.1 && s.1.2),s.2.1,s.2.2.2)) := by
    have both := (Easy.fst (X:=Bool × Bool) (Y:=List Word × Word × Word)).compose (Easy.finite (fun q : Bool × Bool => !q.1 && q.2))
    exact both.poly.pair (by fun_prop)
  exact (init.compose walk_poly).compose get

private theorem walk_append (xs ys : Word) (s : State) : walk (xs++ys) s = walk ys (walk xs s) :=
  List.foldl_append

private theorem frame_complete (bits : Word) (rs : List Word) (cur tail : Word) :
    walk (frame bits) ((true,false),rs,cur,tail) = ((false,false),rs++[cur++bits],[],tail) := by
  induction bits generalizing cur with
  | nil => simp [walk,step]
  | cons b bs ih =>
    change walk (frame bs) ((true,false),rs,cur++[b],tail) = _
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (cur++[b])

private theorem list_complete (rs done : List Word) (tail : Word) :
    walk (ProgramEncoding.encodeRecords rs) ((false,false),done,[],tail) =
      ((false,true),done++rs,[],tail) := by
  induction rs generalizing done with
  | nil => simp [ProgramEncoding.encodeRecords,encodeList,walk,step]
  | cons b bs ih =>
    change walk (frame b++ProgramEncoding.encodeRecords bs) ((true,false),done,[],tail) = _
    rw [walk_append,frame_complete,List.nil_append,ih,List.append_assoc,List.singleton_append]

private theorem tail_complete (xs : Word) (rs : List Word) (cur tail : Word) :
    walk xs ((false,true),rs,cur,tail) = ((false,true),rs,cur,tail++xs) := by
  induction xs generalizing tail with
  | nil => simp [walk]
  | cons b bs ih =>
    change walk bs ((false,true),rs,cur,tail++[b]) = _
    simpa only [List.append_assoc,List.singleton_append] using ih (tail++[b])

theorem read_records (records : List Word) (tail : Word) :
    read (ProgramEncoding.encodeRecords records ++ tail) = (true,records,tail) := by
  simp [read,base,walk_append,list_complete,tail_complete]

end OAI.Computability.MultitapeWeakETH.FrameProgram
