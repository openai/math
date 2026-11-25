import OAI.Computability.IntegerMultiplication.Strip.Index
import OAI.Computability.IntegerMultiplication.Bits.Small

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Dims Adic Loom Code Code.Task
variable {I : Type} {H L i : ℕ}

abbrev headSeq (_i : ℕ) (H _L : I → ℕ) := H
abbrev Dim := Tally × Tally × Tally -- H,L,i
def signs (H L i : ℕ) : Dim := (tally H,tally L,tally i)
abbrev Script := Raw 2 × List (Raw 2) × Raw 2
private def segment (v : Seg L H) := most ((furrow H L).cast v)
def lines (v : Queue H L i) : Script :=
  (most ((flag H).cast v.1),List.ofFn (fun j => segment (v.2.1 j)),most v.2.2)
def badge (x : Queue H L i) :=
  least ((package H L i).cast x)
def flatten_ (v : Script) :=
  (v.1 ++ v.2.1.flatten ++ v.2.2).reverse
theorem easy_flat : Easy flatten_ := by unfold flatten_; fun_prop -- flatten
@[simp] theorem allbits (v : Queue H L i) : (badge v).length=cap i H L := by simp [badge,cap]
theorem rows (s : Span (Seg L H) i) :
    most ((wound 2 (width H L) (segments H L) (furrow H L) i).cast s) =
      (List.ofFn (fun j => segment (s j))).flatten := by
  induction i with
  | zero => rw [wind_none]; simp
  | succ i ih =>
    rw [weave_step, ih, List.ofFn_succ,List.flatten_cons]; rfl
theorem restored (v : Queue H L i) : badge v=flatten_ (lines v) := by
  simp only [badge,least,labels,rows,flatten_,lines]

def rulersH (v : Dim) : Tally := ()::v.1
def rulersK (v : Dim) := rulersH v ++ v.2.1
def panels (v : Dim) (x : Raw 2) := Piecework.segment (v.2.2.map fun _ => rulersK v) x
def cut (v : Dim × Raw 2) : Script :=
  let a := cutLists (rulersH v.1,v.2.reverse)
  let f := panels v.1 a.2
  (a.1,f.1,f.2)
-- can't map param ruler when v bigger; Poly
theorem easyH : Easy rulersH := by unfold rulersH; fun_prop
theorem easyK : Easy rulersK := by have := easyH; unfold rulersK; fun_prop
theorem chamber {X : Type} [Codec X] : Code.Poly (fun i : Tally × X => List.map (fun _ : Unit => i.2) i.1) := by
  simp only [List.map_const']
  apply Poly.of_bound Code.generate
  apply Dom.mul _ _
  · apply (Dom.base _ |>.add (Dom.const _ 1)).mono; intro v; rw [size_prod,size_tally]; omega
  exact (Dom.base _).mono fun v => by rw [show size v = size v.1 + size v.2 + 1 by rcases v with ⟨x,y⟩; simp]; omega
theorem poly_cut : Code.Poly cut := by
  have k : Poly (fun v : Dim × Raw 2 => cutLists (rulersH v.1,v.2.reverse)) :=
    (easy_cut ((Easy.fst.compose easyH).pair (Easy.snd.compose Easy.reverse))).poly
  have x : Poly (fun i:Dim => i.2.2.map fun _ => rulersK i) :=
    (Easy.pair (Easy.snd.compose Easy.snd) easyK |>.poly).compose chamber
  let p := fun v : Dim × Raw 2 => panels v.1 (cutLists (rulersH v.1,v.2.reverse)).2
  have f : Poly p := ((Easy.fst.poly.compose x).pair k.sndCompose).compose Piecework.easy.poly
  exact k.fstCompose.pair (f.fstCompose.pair f.sndCompose)
@[simp] theorem period : (rulersK (signs H L i)).length=width H L := by simp [signs,rulersK,rulersH,width]; omega
theorem underlying {A : Type} (w : Tally) (l : List (List A)) (r : List A)
    (h : ∀g∈l,g.length=w.length) :
    Piecework.segment (List.replicate l.length w) (l.flatten ++ r)=(l,r) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [List.length_cons,List.flatten_cons,List.append_assoc,List.replicate_succ,Piecework.segment]
    rw [Piecework.cut_of_length _ _ _ (h v List.mem_cons_self).symm]
    dsimp only
    rw [ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
theorem peeled (v : Queue H L i) :
    cut (signs H L i, badge v)=lines v := by
  let Y := lines v
  rw [cut,restored]
  dsimp only [flatten_,List.reverse_reverse]
  rw [List.append_assoc,List.reverse_reverse]
  have ha : (rulersH (signs H L i)).length=(lines v).1.length := by
    change _ = (most _).length
    rw [Adic.length]; simp [rulersH,signs]
  rw [Piecework.cut_of_length _ _ _ ha]
  dsimp only
  rw [panels,List.map_const']
  have g : (signs H L i).2.2.length=(lines v).2.1.length := by simp [signs,lines]
  rw [g,underlying]
  intro b hb
  simp only [lines,List.mem_ofFn] at hb
  obtain ⟨_,rfl⟩ := hb
  rw [period,segment, Adic.length]

end Packed

end IntegerMultiplication
end Computability
end OAI
