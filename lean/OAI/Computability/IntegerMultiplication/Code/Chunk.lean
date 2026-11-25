import OAI.Computability.IntegerMultiplication.Code.Slice

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Prog
namespace Piecework
variable {X : Type*}
-- tally lengths determine a partition; last may be incomplete/remainder nonempty
def segment (l : List Tally) (x : List X) : List (List X) × List X :=
  match l with
  | [] => ([],x)
  | a::l => let b := cutLists (a,x)
            let c := segment l b.2
            (b.1::c.1,c.2)
theorem cut_of_length (a : Tally) (x y : List X) (h : a.length=x.length) :
    cutLists (a,x++y)=(x,y) := by simp [cutLists,h]
theorem prescribed (l : List (List X)) :
    segment (l.map (tally ∘ List.length)) l.flatten=(l,[]) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons,segment,List.flatten_cons,Function.comp_apply,cut_of_length _ _ _ (tally_length _)]
    simp [ih] -- c replaced

private def body (c : Cmd) : Cmd :=
  splitRoot 1 (fun _ => give 0 false)
    ((move 1 0 2).join ((pack 0).join (c.join (splitRoot 0 (fun _ => .pass)
      ((move 0 3 2).join ((.again 0 : Cmd).join ((move 3 0 2).join (pack 0))))))))

variable [Codec X]
private theorem spend (C : ℕ) (t u v _d a b : ℕ) (h : a+b=t+1) (j : 0<a) (n : 0<u) :
    42*u+(1+(C*(u+a+1)+(42*a+(((2*C+256)*(v+b)+1)+(42*a+1+2)+2)+2+4)+2)+2)+2+4≤
      (2*C+256)*(u+v+1+t) := by
  -- each term C*u fits, C*a charged via consumed t-b=a-1; if a=1 empty data, rely u≥? charged slack and extra +1 consumed outer
  have ha : b≤t := by omega
  have hj : C*b ≤ C*t := Nat.mul_le_mul_left C ha
  have hk : C ≤ C*u := Nat.le_mul_of_pos_right C n
  have hd := congrArg (C * ·) h
  have hv : C*a+C*b=C*t+C := by simpa [Nat.mul_add] using hd
  -- C*(1+overcount) maybe: RHS-LHS coeff in C =2(C(u+v+1+t))-C(u+a+1)-2C(v+b)
  -- = C(u+a-1) nonneg. constants similarly
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
  omega

private theorem chunk {c C} (hc : ∀ (x : Tally × List X) G r,
    Fits G c (pile 0 (send x) r) (pile 0 (send (cutLists x)) r)
      (C*(size x.1+size (cutLists x).1+1))) (l : List Tally) (x : List X) (env : Env) (r : Deck) :
    Fits (body c::env) (body c)
      (pile 1 (send l) (pile 0 (send x) r))
      (pile 0 (send (segment l x).1) (pile 0 (send (segment l x).2) r))
      ((2*C+256)*(size l+size x)) := by
  induction l generalizing x r with
  | nil =>
    refine (fits_bit (b:=false) (c:=fun _ => give 0 false) (fits_give false ..)).mono ?_
    rw [size_nil,Nat.add_mul,Nat.mul_add 256]
    omega
  | cons u l ih =>
    let G := body c :: env
    let z := pile 1 (send l) r
    obtain ⟨a,b,e⟩ : ∃ a b, cutLists (u,x)=(a,b) := ⟨_,_,rfl⟩
    have g : size a+size b=size x+1 := by
      injection e with d f
      change x.take u.length = a at d
      change x.drop u.length = b at f
      subst a; subst b
      rw [← size_append_right, List.take_append_drop]
    have h₁ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) (send u) G (pile 0 (send x) z)
    have h₂ := fits_pack (send u) (send x) z 0 G
    have h₃ := hc (u,x) G z
    rw [e, send_prod, send_prod] at h₃
    have h₄ := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) (send a) G (pile 0 (send b) z)
    dsimp only [z] at h₄ h₃ h₂ h₁
    have hi := ih b (pile 3 (send a) r)
    rw [pile_comm 3 _ _ 0 _ (by decide),
        pile_comm 3 _ r 1 _ (by decide),
        pile_comm 0 (send b) (pile 3 (send a) r) 1 _ (by decide)] at h₄
    have h₅ := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) (send a) G
      (pile 0 (send (segment l b).1) (pile 0 (send (segment l b).2) r))
    rw [pile_comm 3 _ _ 0 _ (by decide),pile_comm 3 _ _ 0 _ (by decide)] at h₅
    have he := h₁.join (h₂.join (h₃.join (fits_pair (c:=fun _ => .pass) (h₄.join (hi.again0.join (h₅.join (fits_pack ..)))))))
    rw [pile_comm 0 (send x) r 1 _ (by decide)] at he -- only in input, good
    simp only [segment,e,send_cons,size_cons]
    apply (fits_pair he).mono
    change 42*size u+(1+(C*(size u+size a+1)+(42*size a+(((2*C+256)*(size l+size b)+1)+
        (42*size a+1+2)+2)+2+4)+2)+2)+2+4 ≤ _
    exact spend C (size x) (size u) (size l) 0 (size a) (size b) g (size_pos _) (size_pos _)

theorem easy : Easy (fun i : List Tally × List X => segment i.1 i.2) := by
  obtain ⟨c,C,h⟩ := (Computes.cut (X:=X))
  refine ⟨splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((Prog.tie (body c)).join (pack 0))), 2*C+400, ?_⟩
  rintro ⟨l,x⟩ E r
  have H := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) (send l) E (pile 0 (send x) r)
  have e := chunk (C:=C) h l x E r
  apply (fits_pair (H.join (e.tie.join (fits_pack ..)))).mono
  change 42*size l+(((2*C+256)*(size l+size x)+1)+1+2)+2+4 ≤ _
  simp only [size_prod,Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

@[fun_prop]
theorem easySegment {Y} [Codec Y] {g : Y→List Tally} {h : Y→List X} (e : Easy g) (f : Easy h) :
    Easy (fun y => segment (g y) (h y)) := (Easy.pair e f).compose easy
end Piecework
end Code

end IntegerMultiplication
end Computability
end OAI
