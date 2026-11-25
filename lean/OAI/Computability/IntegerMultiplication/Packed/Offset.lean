import OAI.Computability.IntegerMultiplication.Packed.Mixture

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Adic Code
variable {H L i : ℕ}
abbrev digit (x : Seg L H) := x.2.2
def toll (s : Raw 2) := s.reverse.headD 0
theorem toll_reads (x : Seg L H) :
    toll (most ((furrow H L).cast x))=x.2.2 := by simp [toll,furrow_word]
theorem facile_toll : Easy toll := by
  have e : Easy (fun x : Raw 2 => x.headD 0) := by
    -- defeq listCase maybe
    have h := Easy.listCase (X:=Fin 2) (0:Fin 2) Easy.fst
    suffices hh : (fun x : Raw 2 => x.headD 0) = (fun x => List.casesOn (motive:=fun _=>Fin 2) x 0 fun u _ => u) from hh ▸ h
    funext x; cases x <;> rfl
  exact Easy.reverse.compose e
def coin (t : Turn) (s : Fin 2 × Fin 2) : Fin 2 :=
  if (s.1.val:ℤ)=1 ∧ (s.2.val:ℤ)=t.test then 1 else 0
abbrev coin_ (s t : Seg L H) (x) := coin x (digit s,digit t)
theorem mapped (s t : Queue H L i) (j : Fin i) (x : Turn) :
    start x s t j = x.shift * (coin_ (s.2.1 j) (t.2.1 j) x).val := by
  unfold start compare_ phase coin_ coin digit
  rw [parity]
  dsimp only
  have t := (t.2.1 j).2.2.isLt
  split
  next v =>
    rw [ite_eq_left (by constructor <;> omega)]; simp
  next v => rw [ite_eq_right (by rintro ⟨a,b⟩; apply v; constructor <;> omega)]; simp

def empty_ (l : Raw 2) : Raw 2 := fill 0 (ruler l)
@[simp] theorem empty_len (l : Raw 2) : (empty_ l).length=l.length := by simp [empty_,fill_eq]
@[simp] theorem empty_rev (l : Raw 2) : (empty_ l).reverse=empty_ l := by simp [empty_,fill_eq]
@[simp] theorem empty_val (l : Raw 2) : code (empty_ l)=0 := by
  suffices e : ∀ n, code (List.replicate n (0:Fin 2))=0 by simp [empty_,fill_eq,e]
  intro n; induction n with
  | zero => simp [code]
  | succ n ih => simp [code,List.replicate_succ,ih]

def onehot (t) (p : Raw 2 × Raw 2) :=
  empty_ p.1.tail ++ [coin t (toll p.1,toll p.2)]
theorem easy_onehot (t) : Easy (onehot t) := by
  have h := facile_toll
  have e : Easy (fun p : Raw 2 => p.tail) := by
    suffices z : (fun p : Raw 2 => p.tail)=(fun x => List.casesOn (motive:=fun _=>Raw 2) x [] (fun _ a => a)) from
      z ▸ (Easy.listCase _ Easy.snd)
    funext x; cases x <;> rfl
  have u := Easy.finite (coin t)
  have f : Easy (fun p : Raw 2 × Raw 2 => coin t (toll p.1,toll p.2)) :=
    ((Easy.fst.compose h).pair (Easy.snd.compose h)).compose u
  have v : Easy (fun p : Raw 2 × Raw 2 => p.1.tail) := Easy.fst.compose e
  unfold onehot empty_
  fun_prop
theorem hot_value (t : Turn) (w z : Seg L H) :
    let l := onehot t (most ((furrow H L).cast w),most ((furrow H L).cast z))
    code (l.reverse)=(coin_ w z t).val ∧ l.length=width H L := by
  dsimp only
  have hv : 0<width H L := by unfold width; omega
  simpa [onehot, Adic.length,toll_reads,code,coin_,digit] using
    (show width H L - 1 + 1 = width H L by omega)

def loose (t : Turn) (p : Script × Script) : Script :=
  (empty_ p.1.1, lock (onehot t) [] [] (p.1.2.1,p.2.2.1), empty_ p.1.2.2)
theorem easy_loose (t) : Easy (loose t) := by
  have e := Code.easy_lock _ (easy_onehot t) ([]:Raw 2) []
  let u := fun p : Script × Script => (p.1.2.1,p.2.2.1)
  have v : Easy u := by unfold u; fun_prop
  have z := v.compose e
  unfold loose empty_
  apply Easy.pair (by fun_prop); exact z.pair (by fun_prop)

private theorem stated {A B C : Type} [Codec A] [Codec B] [Codec C] (f : A×B→C) (a b) (x : Fin i→A) (y : Fin i→B) :
    lock f a b (List.ofFn x,List.ofFn y)=List.ofFn (fun j => f (x j,y j)) := by
  have e : ∀ {A : Type} (x : Fin i→A), (Series.natural i).tab x=List.ofFn x := by
    intro A x; unfold Series.natural Series.tab Series.fixed
    -- finRange is ofFn id
    change List.map x (List.ofFn id) = _
    rw [List.map_ofFn]
    rfl
  simpa only [e] using (paired (X:=A) f x y (Series.natural i) a b) -- needs Codec? included section [Codec] in paired. create noncomputable instance arbitrary constant tree
def unsigned (t : Turn) (p : Dim × (Raw 2 × Raw 2)) : Raw 2 :=
  flatten_ (loose t (cut (p.1,p.2.1),cut (p.1,p.2.2)))
theorem poly_us (t) : Poly (unsigned t) := by
  have h : Poly (fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.1)) := by fun_prop
  have g : Poly (fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.2)) := by fun_prop
  exact ((h.compose poly_cut).pair (g.compose poly_cut)).compose ((easy_loose t |>.compose easy_flat).poly)

private theorem worth (t : Turn) (a b : Fin i→Seg L H) :
    let l := List.ofFn (fun j : Fin i => onehot t (most ((furrow H L).cast (a j)),
      most ((furrow H L).cast (b j))))
    l.flatten.length=i*width H L ∧ (code (l.flatten.reverse):ℤ)=sumSeq H L i
      (fun j => ((coin_ (a j) (b j) t).val:ℤ)) := by
  dsimp only
  induction i with
  | zero => simp [Adic.code,sumSeq]
  | succ i ih =>
    rw [List.ofFn_succ]
    obtain ⟨e,h⟩ := ih (fun j=>a j.succ) (fun j=>b j.succ)
    have ⟨v,u⟩ := hot_value t (a 0) (b 0)
    simp only [List.flatten_cons,List.length_append,u,e,Nat.add_mul,Nat.one_mul,List.reverse_append,
      Adic.cat,List.length_reverse,v,sumSeq,Nat.cast_add,Nat.cast_mul,h]
    simp only [add_comm]
    simp
private theorem sum_shift (r : ℤ) (a : Span ℤ i) :
    sumSeq H L i (fun j => r*a j) = r*sumSeq H L i a := by
  induction i with
  | zero => simp [sumSeq]
  | succ i ih => simp only [sumSeq]; rw [ih]; ring
theorem weight (t : Turn) (x y : Queue H L i) :
    let z := unsigned t (signs H L i,badge x,badge y)
    z.length=cap i H L ∧
      t.shift*(code z:ℤ)= (2^L:ℕ)*sumSeq H L i (start t x y) := by
  dsimp only
  simp only [unsigned,peeled,loose,lines,stated,flatten_,List.reverse_append]
  let l := List.ofFn fun j : Fin i => onehot t (most ((furrow H L).cast (x.2.1 j)),
    most ((furrow H L).cast (y.2.1 j)))
  change ((empty_ (most x.2.2)).reverse ++ (l.flatten.reverse ++ _)).length=_ ∧
    t.shift* (code ((empty_ (most x.2.2)).reverse ++ (l.flatten.reverse ++ _)) : ℤ)=_
  obtain ⟨u,v⟩ := worth t x.2.1 y.2.1
  change l.flatten.length=_ at u
  change (code l.flatten.reverse:ℤ)=_ at v
  simp only [empty_rev,List.length_append,List.length_reverse,empty_len,u,Adic.length,Adic.cat,empty_val,v,
    Nat.cast_mul,mul_zero,add_zero,zero_add]
  constructor
  · unfold width cap; ring
  rw [show start t x y = fun j => t.shift*(coin_ (x.2.1 j) (y.2.1 j) t).val from funext fun j => mapped x y j t, sum_shift]
  rw [mul_left_comm]

end Packed

end IntegerMultiplication
end Computability
end OAI
