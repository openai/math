import OAI.Computability.IntegerMultiplication.Loom.Arrivals

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Loom Strip Dims Adic
variable {p n m i : ℕ}
def tile (p n m) : Adopt ((line p n).cart (line p m)) (line p (n+m)) :=
  ⟨binary p n m,fun {_} => Adic.schedule⟩

-- expand relation by heterogeneous list:
private def scan : (l : Tape) → Pin l → List ℕ
| [],_ => []
| a::l,i => (look (n:=a) (l:=l) i).1.val :: scan l (look (n:=a) (l:=l) i).2
private theorem union_ (l t : Tape) (i : Pin l) (j : Pin t) :
    scan (l++t) (Union l t (i,j))=scan l i ++ scan t j := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨b,c⟩ := i
    change b.val :: scan (l++t) (Dims.Union l t (c,j)) = b.val::(scan l c ++ scan t j)
    rw [ih]

private theorem tiled (x : Block p n) : scan (field p n) x = (most x).map Fin.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨a,c⟩ := x
    change a.val :: scan _ c = a.val :: _
    rw [ih]; rfl

theorem tile_most (x : Block p n) (y : Block p m) :
    most ((tile p n m).cast (x,y)) = most x ++ most y := by
  apply (List.map_injective_iff.mpr Fin.val_injective)
  rw [List.map_append,← tiled,← tiled,← tiled]
  unfold tile Adic.binary
  rw [Equiv.trans_apply]
  -- generalized cast
  have h {l s : Tape} (e:l=s) (i : Pin l) :
      scan s ((Equiv.cast (congrArg Pin e)) i) = scan l i := by subst s; rfl
  erw [h]
  apply union_
  exact (field_add ..).symm
theorem tile_n (x : Block p n) (y : Block p m) :
    number ((tile p n m).cast (x,y))=p^m*number x + number y := by
  simp only [number,least,tile_most,List.reverse_append,Adic.cat,List.length_reverse,Adic.length]
  rw [Nat.add_comm]

def castN (p n m : ℕ) (h:n=m) : Adopt (line p n) (line p m) :=
  h ▸ Adopt.same _
theorem castN_most (x : Block p n) (h : n=m) :
    most ((castN p n m h).cast x) = most x := by subst m; rfl
theorem castN_n (x : Block p n) (h : n=m) :
    number ((castN p n m h).cast x) = number x := by simp [number,least,castN_most]

variable (p n : ℕ) {A : Type} (x : Series A)
-- n repeats embedding Track to block segmentation, uniform formulas.
abbrev weave := (Track x)
def wound (d : Adopt x (line p n)) :
    (i : ℕ) → Adopt (Track x i) (line p (i*n))
| 0 => (park x (field p n) d 0).thenDo (show Adopt (layout (Rack (field p n) 0)) (line p (0*n)) by rw [Nat.zero_mul]; exact Adopt.same _)
| i+1 =>
  let t := (step x i).thenDo (d.split (wound d i))
  (t.thenDo (tile p n (i*n))).thenDo (castN p _ _ (by ring))
variable {p n}
@[simp] theorem wind (d : Adopt x (line p n)) (r : Fin (i+1)→A) :
    number ((wound p n x d (i+1)).cast r) =
      p^(i*n)*number (d.cast (r 0))+number ((wound _ _ _ d i).cast (fun j:Fin i => r j.succ)) := by
  change number ((castN p _ _ _).cast ((tile p n (i*n)).cast (_, _))) = _
  rw [castN_n,tile_n]; rfl
@[simp] theorem weave_step (d : Adopt x (line p n)) (r : Fin (i+1)→A) :
    most ((wound p n x d (i+1)).cast r) =
      most (d.cast (r 0)) ++ most ((wound _ _ _ d i).cast (fun j:Fin i => r j.succ)) := by
  change most ((castN p _ _ _).cast ((tile p n (i*n)).cast (_, _))) = _
  rw [castN_most,tile_most]; rfl
theorem wind_none (d : Adopt x (line p n)) (r : Fin 0→A) :
    most ((wound p n x d 0).cast r)=[] :=
  List.length_eq_zero_iff.mp (by rw [Adic.length,Nat.zero_mul])
theorem wind_naught (d : Adopt x (line p n)) (r : Fin 0→A) :
    number ((wound p n x d 0).cast r)=0 := by simp [number,least,wind_none,Adic.code]

-- a chunk of H+1+L=K bits; chosen bit (offset L, counted from LSU) embedded between. use Fin 2.
variable (H L : ℕ)
abbrev width := H+1+L
abbrev Top (h : ℕ) := Block 2 h × Fin 2
abbrev Tail (b : ℕ) := Block 2 b
abbrev Chunk := Top H × Tail L
abbrev dart := (line 2 H).cart (Series.natural 2)
abbrev chunks := (dart H).cart (line 2 L)
def chip (p : ℕ) : Adopt (Series.natural p) (line p 1) :=
  (Adopt.skip _).back.thenDo (Adopt.turn _ (hinge p []))
def flag : Adopt (dart H) (line 2 (H+1)) :=
  ((Adopt.same _).split (chip 2)).thenDo (tile 2 H 1)
def chord : Adopt (chunks H L) (line 2 (width H L)) :=
  ((flag H).split (Adopt.same _)).thenDo (tile 2 (H+1) L)
abbrev Seg L H := Tail L × Top H
abbrev segments := (line 2 L).cart (dart H)
def furrow : Adopt (segments H L) (line 2 (width H L)) :=
  (((Adopt.same _).split (flag H)).thenDo (tile 2 L (H+1))).thenDo (castN 2 _ _ (by unfold width; omega))
theorem chip_word (f : Fin p) :
    most ((chip p).cast f)=[f] := rfl
theorem chip_n (f : Fin p) :
    number ((chip p).cast f)=f.val := by simp [number,least,chip_word,Adic.code]
theorem flag_word (f : Top H) :
    most ((flag H).cast f) = most f.1 ++ [f.2] := by
  change most ((tile _ _ _).cast (_, _))= _
  rw [tile_most]; rfl
theorem flag_n (f : Top H) :
    number ((flag H).cast f)=2*number f.1+f.2.val := by
  change number ((tile 2 _ _).cast (_, _))= _
  rw [tile_n, pow_one,chip_n]; rfl
def guardBlock := ((line 2 L).cart (line 2 H))
def guard (x : Seg L H) : Block 2 (L+H) := (tile 2 L H).cast (x.1,x.2.1)
theorem furrow_word (x : Seg L H) :
    most ((furrow H L).cast x)=most (guard H L x) ++ [x.2.2] := by
  change most ((castN _ _ _ _).cast ((tile 2 _ _).cast (_, _)))= _
  rw [castN_most,tile_most,flag_word,guard,tile_most,List.append_assoc]; rfl
theorem furrow_n (x : Seg L H) :
    number ((furrow H L).cast x)=2*number (guard H L x)+x.2.2.val := by
  change number ((castN _ _ _ _).cast ((tile 2 L _).cast (x.1, (flag H).cast x.2)))= _
  rw [castN_n,tile_n,flag_n,guard,tile_n,pow_succ]; ring
end Packed

end IntegerMultiplication
end Computability
end OAI
