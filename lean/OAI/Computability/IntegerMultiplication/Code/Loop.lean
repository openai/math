import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic
import OAI.Computability.IntegerMultiplication.Code.FoldLeft
import OAI.Computability.IntegerMultiplication.Code.Slice

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

section Basic
variable {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z]
/-- Fold over a stored list. Intermediate sizes must be bounded---we state a very coarse
version in exponent form, since we will most often apply this lemma in calls with
polynomial bookkeeping. -/
theorem Poly.fold_left {f : X × Y → X} (hp : Poly f)
    (C k : ℕ)
    (h : ∀ (s : List Y × X) (l : List Y), l <+: s.1 →
      size (l.foldl (fun x y => f (x,y)) s.2) ≤ C*(size s+1)^k) :
    Poly (fun i : List Y × X => i.1.foldl (fun x y => f (x,y)) i.2) := by
  let W := List Y × X
  let acc (l : List Y) (x : W) :=
    (x.1.take (x.1.length - l.length)).foldl (fun x y => f (x,y)) x.2
  let w (l) (x : W) := send (acc l x)
  let D (l) (x : W) := l <:+ x.1
  let Q := {i : Y × List Y × W // D (i.1::i.2.1) i.2.2}
  let L (i : Q) := size i.val.2.2
  let input : Q → Y × X := fun i => (i.val.1,acc (i.val.1 :: i.val.2.1) i.val.2.2)
  have hsz : Dom L fun i => size (input i) := by
    apply Dom.mono (((Dom.base L).add (Dom.mul (Dom.const L C) (((Dom.base L).add (Dom.const L 1)).pow k))).add (Dom.const L 1))
    intro i
    have hh := h i.val.2.2 (i.val.2.2.1.take _) (List.take_prefix (i.val.2.2.1.length-(i.val.2.1.length+1)) _)
    change size _ ≤ C*(L i+1)^k at hh
    simp only [input,size_prod,acc,List.length_cons]
    have hz : size i.val.1 ≤ L i := by
      change _ ≤ size (X:=List Y × X) _
      suffices e : size i.val.1 ≤ size i.val.2.2.1 by simp; omega
      have his : i.val.1 ∈ i.val.2.2.1 := i.property.subset List.mem_cons_self
      have his' := List.single_le_sum (l := (i.val.2.2.1).map size) (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem (f:=size) his)
      simp [← costSum_le_length_size]
      change _ ≤ _ + (List.map size i.val.2.2.1).sum + 1
      omega
    omega
  obtain ⟨b,hb,hr⟩ := ((Easy.exchange.poly.compose hp).on hsz)
  obtain ⟨j,M,hm⟩ := hb
  let t (i : W) := M*(size i+1)^j
  have hs := Task.sweep (p:=fun (_ : W) => send) (w:=w) (a:=fun _ _ i => t i) (D:=D)
    (fun v l y ⟨q,hq⟩ => ⟨q++[v],by simpa using hq⟩)
    (show Task _ _ _ from (hr.mono hm).conform (by intro; rfl) (fun i => ?_) (fun i => ?_))
  apply Poly.of_bound (p := fun x => Task.foldCost (fun v _ => t x+size v) x.1)
    ((hs.on (fun i : W => ⟨(i.1,i),List.suffix_rfl⟩)).conform (by intro; rfl) (fun i => by rcases i with ⟨l,u⟩; simp [w,acc] ; rfl
       )
      (fun _ => by simp [w,acc]))
  · -- fold cost = #iterations * t x + size forest
    have eq (x : W) : ∀ (l : List Y), Task.foldCost (fun v l => t x+size v) l =
      t x*l.length + size l := by
      intro l
      induction l <;> simp_all [Task.foldCost,Nat.mul_add]; omega
    refine (((Dom.mul (Dom.const size M) (((Dom.base size).add (Dom.const size 1)).pow j)).mul (Dom.base size)).add (Dom.base size)).mono ?_
    intro i
    have hi : size (X:=W) i = size i.1+size i.2+1 := rfl
    rw [eq]
    have he := costSum_le_length_size i.1
    simp only [t,hi]
    gcongr <;> omega
  · exact send_prod _
  · rcases i with ⟨⟨v,l,i⟩,a⟩
    change send (f (acc (v::l) i,v)) = send (acc l i)
    congr 1
    obtain ⟨r,he⟩ := a
    dsimp at he
    have hh : (r ++ v::l).take (r.length+1)=r++[v] := by rw [List.take_append]; simp
    simp only [acc, ← he,List.length_append,List.length_cons,Nat.add_sub_cancel]
    rw [show r.length+(l.length+1)-l.length = r.length+1 by omega]
    simp [hh,List.foldl_append]

end Basic
end Code

end IntegerMultiplication
end Computability
end OAI
