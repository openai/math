import OAI.Computability.IntegerMultiplication.Invalid

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Code Strip Adic
variable {H L i : ℕ}
private def ending (t : Fin 2) (l : Raw 2) :=
  ((t:: (cutLists (tally 1,l.reverse)).2): Raw 2).reverse
private def amend (x : Raw 2 × Raw 2) :=
  ending (other (toll x.2) (toll x.1)) x.2
private theorem easy_amend : Easy amend := by
  have h : Easy (fun z : Fin 2 × Raw 2 => ending z.1 z.2) := by
    have v := easy_cut ((Easy.const (tally 1)).pair
      (Easy.snd (X:=Fin 2) (Y:=Raw 2) |>.compose Easy.reverse)) |>.sndCompose
    exact ((Easy.fst.pair v).compose Easy.cons).compose Easy.reverse
  exact (((Easy.snd (X:=Raw 2) (Y:=Raw 2) |>.compose facile_toll).pair (Easy.fst.compose facile_toll)
    |>.compose (Easy.finite (fun i : Fin 2 × Fin 2 => other i.1 i.2))
    |>.pair Easy.snd).compose h)
private theorem amends (s t : Seg L H) :
    amend (most ((furrow H L).cast s),most ((furrow H L).cast t)) =
      most ((furrow H L).cast (t.1,t.2.1,other t.2.2 s.2.2)) := by
  rw [amend,toll_reads,toll_reads,furrow_word,furrow_word H L _,furrow_word]
  simp [ending,cutLists]
  rfl

def white (x : Script × Script) : Script :=
  (x.2.1, lock amend [] [] (x.1.2.1,x.2.2.1), x.2.2.2)
theorem lamp (x y : Queue H L i) :
    white (lines x,lines y) = lines (guide x y) := by
  -- use stated via map series here
  have e {A B C : Type} [Codec A] [Codec B] [Codec C] (v : Fin i → A) (w : Fin i → B)
      (f : A×B→C) a b :
      lock f a b (List.ofFn v,List.ofFn w)=List.ofFn (fun j => f (v j,w j)) := by
    have e : ∀ {A : Type} (x : Fin i→A), (Series.natural i).tab x=List.ofFn x := by
      intro A x; unfold Series.natural Series.tab Series.fixed
      change List.map x (List.ofFn id)=_; rw [List.map_ofFn]; rfl
    simpa only [e] using (paired (X:=A) f v w (Series.natural i) a b)
  unfold white lines
  dsimp only
  rw [e]
  -- guide folds
  refine Prod.ext (by rfl) (Prod.ext ?_ (by rfl))
  simp only
  apply congrArg List.ofFn
  funext j
  exact amends ..

def bright (a : Dim × Raw 2 × Raw 2) :=
  flatten_ (white (cut (a.1,a.2.1),cut (a.1,a.2.2)))
theorem easy_bright : Poly bright := by
  suffices t : Easy white from
    (((by fun_prop : Poly fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.1)).compose poly_cut).pair
      ((by fun_prop : Poly fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.2)).compose poly_cut)).compose
        ((t.compose easy_flat).poly)
  have e := Code.easy_lock _ easy_amend ([]:Raw 2) []
  let u := fun p : Script × Script => (p.1.2.1,p.2.2.1)
  have v : Easy u := by unfold u; fun_prop
  exact ((by fun_prop : Easy (fun x : Script×Script=>x.2.1))).pair
    ((v.compose e).pair (by fun_prop))
theorem bright_eq (x y : Queue H L i) :
    bright (signs H L i,badge x,badge y)=badge (guide x y) := by
  simp only [bright,peeled,lamp,← restored] -- restored Packed, Mirror

def title (p : Fin 2) : Bool := decide (p=1)
abbrev Act := Triple (Raw 2)
def emblem (x : Act) :=
  (x.1.map title) ++ (x.2.1.map title) ++ x.2.2.map title
theorem easy_emblem : Easy emblem := by
  have := Easy.finite title
  unfold emblem; fun_prop
def names (x : Plate H L i) : Act :=
  (badge x.1,badge x.2.1,badge x.2.2)

theorem title_identify : Function.Injective title := by
  intro a b; fin_cases a <;> fin_cases b <;> decide
theorem size_key (x : Plate H L i) :
    (emblem (names x)).length = 3*cap i H L := by simp [emblem,names]; ring
theorem identify : Function.Injective (emblem ∘ (names (H:=H) (L:=L) (i:=i))) := by
  rintro ⟨x,y,u⟩ ⟨x',y',u'⟩ e
  unfold Function.comp emblem names at e
  have sep {a b c d : List Bool} (g : a.length=b.length) (e : a++c=b++d) : a=b ∧ c=d := by
    have x := congrArg (List.take a.length) e
    have y := congrArg (List.drop b.length) e
    rw [List.take_left,g,List.take_left] at x
    rw [List.drop_left,← g,List.drop_left] at y
    exact ⟨x,y⟩
  simp only [List.append_assoc] at e
  obtain ⟨xv,e⟩ := sep (show (List.map title (badge x)).length=(List.map title (badge x')).length by simp) e
  obtain ⟨yv,uv⟩ := sep (show (List.map title (badge y)).length=(List.map title (badge y')).length by simp) e
  have hi : Function.Injective (List.map title ∘ @badge _ _ i) := List.map_injective_iff.mpr title_identify
    |>.comp (fun x y h => (package H L i).cast.injective
      (number_inj 2 (cap i H L) (congrArg Adic.code h)))
  exact Prod.ext (hi xv) (Prod.ext (hi yv) (hi uv))

end Packed

end IntegerMultiplication
end Computability
end OAI
