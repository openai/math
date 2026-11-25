import OAI.Computability.NearSquareRoot.InterchangeRequestHeader
import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal

/-! # Compiling the unary loop bounds of a leaf interchange from its shape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeafMasksShape

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic NearSquareRoot.InterchangeAddress
  NearSquareRoot.Space NearSquareRoot.InterchangeSpace

abbrev Header := Tally × Tally × List Tally × List Tally × List Tally

def descriptor {b : ℕ} (x : Request b) : Header :=
  (tally b,tally x.width,shape x.before,shape x.between,shape x.after_)

/-- Include the number of rows traversed after fixing the first active digit. -/
def rulers {b : ℕ} (x : Request b) : Tally × Tally × Tally × Tally × Tally :=
  let d := (line b x.width).count
  let g := (layout x.between).count
  let z := (layout x.after_).count
  (tally (layout x.before).count,tally d,tally g,tally z,tally (g*(d*z)))

def cost {b : ℕ} (x : Request b) : ℕ := x.rows.count + (size (descriptor x)+1)^2

private theorem sized {I : Type} {cost t : I → ℕ} {p q : I → Tree}
    (h : Task t p q) (ht : ∀ i, t i ≤ cost i) : Sized (fun i => (cost i : ℝ)+1) p q :=
  (Sized.natural h).mono (fun i => by exact_mod_cast Nat.add_le_add_right (ht i) 1)

private theorem counts (p d g b : ℕ) (hp : 0 < p) (hd : 0 < d)
    (hg : 0 < g) (hb : 0 < b) :
    let N := p*(d*(g*(d*b)))
    p ≤ N ∧ d ≤ N ∧ g ≤ N ∧ b ≤ N ∧ g*(d*b) ≤ N := by
  let tail := g*(d*b)
  have hi : 0 < tail := Nat.mul_pos hg (Nat.mul_pos hd hb)
  have h1 := Nat.le_mul_of_pos_left (d*tail) hp
  have h2 := Nat.le_mul_of_pos_left tail hd
  have h3 := Nat.le_mul_of_pos_left (d*b) hg
  have h4 := Nat.le_mul_of_pos_left b hd
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.mul_pos hd hi), (Nat.le_mul_of_pos_right d hi).trans h1,
    (Nat.le_mul_of_pos_right g (Nat.mul_pos hd hb)).trans (h2.trans h1),
    h4.trans (h3.trans (h2.trans h1)),h2.trans h1⟩

/-- One program reads the varying radix and request descriptor. The four
individual bounds and the combined suffix bound are all unary tallies. -/
theorem prepare_solid {I : Type} (b : I → ℕ) (x : (i : I) → Request (b i))
    (hb : ∀ i, 2 ≤ b i)
    (valid : ∀ i, solid (x i).before ∧ solid (x i).between ∧ solid (x i).after_) :
    BoundedTask (fun i => cost (x i)) (fun i => cost (x i))
      (fun i => .fork (send (tally (b i))) (x i).header) (fun i => send (rulers (x i))) := by
  let h (i : I) := descriptor (x i)
  let fuel (i : I) := cost (x i)
  let budget (i : I) : ℝ := (fuel i : ℝ) + 1
  let p i := (x i).before
  let f i := field (b i) (x i).width
  let g i := (x i).between
  let z i := (x i).after_
  have one : ∀ i, 1 ≤ budget i := fun i => by simp [budget]
  have hv : Volume budget (fun i => send (h i)) := by
    refine ⟨1,fun i => ?_⟩
    have H : size (h i) ≤ fuel i := by
      change size (h i) ≤ (x i).rows.count + (size (h i)+1)^2
      nlinarith [Nat.zero_le (size (h i)*size (h i))]
    change (size (h i) : ℝ) ≤ ((1:ℕ):ℝ) * budget i
    simp only [Nat.cast_one,one_mul,budget]
    exact_mod_cast H.trans (Nat.le_succ _)
  have read {T : Type} [Codec T] (get : Header → T) (easy : Easy get) :
      Carries budget (fun i => send (h i)) (fun i => send (get (h i))) :=
    Carries.func one hv get easy
  have pa := read (fun y => y.2.2.1) (by fun_prop)
  have ga := read (fun y => y.2.2.2.1) (by fun_prop)
  have za := read (fun y => y.2.2.2.2) (by fun_prop)
  let operands (i : I) := (tally (x i).width,tally (b i))
  have fw := read (fun y => (y.2.1,y.1)) (by fun_prop)
  have rep (b w : ℕ) : field b w = List.replicate w b := by
    induction w <;> simp_all [field, List.replicate_succ]
  have built : Carries budget (fun i => send (h i)) (fun i => send (shape (f i))) := by
    apply fw.sequence
    have mk := (Code.generate (X:=Tally)).on operands
    have defn (i : I) : shape (f i) = List.replicate (operands i).1.length (operands i).2 := by
      simp [f,shape,rep,operands]
    simp_rw [defn]
    apply sized mk
    intro i
    have hw : (operands i).1.length+1 ≤ size (h i)+1 := by
      simp only [h,descriptor,operands,tally_length,size_prod,size_tally]
      omega
    have hm : size (operands i).2 ≤ size (h i)+1 := by
      simp only [h,descriptor,operands,size_prod]
      omega
    exact (Nat.mul_le_mul hw hm).trans (by change _ ≤ (x i).rows.count + (size (h i)+1)^2; rw [sq]; omega)
  have actual (i : I) : (x i).rows.count = room (p i)*(room (f i)*(room (g i)*(room (f i)*room (z i)))) := by
    change ((layout (p i)).cart ((layout (f i)).cart ((layout (g i)).cart
      ((layout (f i)).cart (layout (z i)))))).count = _
    simp only [Series.count_cart,space]
  have solids (i : I) : solid (p i) ∧ solid (f i) ∧ solid (g i) ∧ solid (z i) := by
    refine ⟨(valid i).1,?_,(valid i).2.1,(valid i).2.2⟩
    intro d hd
    change d ∈ field (b i) (x i).width at hd
    rw [rep] at hd
    exact (List.eq_of_mem_replicate hd) ▸ hb i
  have fit i := counts (room (p i)) (room (f i)) (room (g i)) (room (z i))
    (wide _ (solids i).1) (wide _ (solids i).2.1) (wide _ (solids i).2.2.1) (wide _ (solids i).2.2.2)
  have cap (s : I → Tape) (ok : ∀ i, solid (s i)) (bound : ∀ i, room (s i) ≤ (x i).rows.count)
      (src : Carries budget (fun i => send (h i)) (fun i => send (shape (s i)))) :
      Carries budget (fun i => send (h i)) (fun i => send (tally (room (s i)))) :=
    src.sequence <| sized (Dims.unary.on (fun i => ⟨s i,ok i⟩))
      (fun i => (bound i).trans (Nat.le_add_right _ _))
  have pp := cap p (fun i => (solids i).1) (fun i => (actual i) ▸ (fit i).1) pa
  have ff := cap f (fun i => (solids i).2.1) (fun i => (actual i) ▸ (fit i).2.1) built
  have gg := cap g (fun i => (solids i).2.2.1) (fun i => (actual i) ▸ (fit i).2.2.1) ga
  have zz := cap z (fun i => (solids i).2.2.2) (fun i => (actual i) ▸ (fit i).2.2.2.1) za
  let tail (i : I) := g i ++ (f i ++ z i)
  let shapes (i : I) := (shape (g i),shape (f i),shape (z i))
  let append3 := fun y : List Tally × List Tally × List Tally => y.1 ++ (y.2.1 ++ y.2.2)
  have tailRead : Carries budget (fun i => send (h i)) (fun i => send (shape (tail i))) := by
    have triple : Carries budget (fun i => send (h i)) (fun i => send (shapes i)) :=
      ga.twice (built.twice za)
    have concat := triple.chain (Carries.func one triple.out append3 (by unfold append3; fun_prop))
    simpa only [shapes,tail,append3,shape,List.map_append] using concat
  have tt := cap tail (fun i => (solid_cat ..).mpr ⟨(solids i).2.2.1,
      (solid_cat ..).mpr ⟨(solids i).2.1,(solids i).2.2.2⟩⟩) (fun i => by
        simp only [actual,tail,room_cat]; exact (fit i).2.2.2.2) tailRead
  have out := carries_bounded (pp.twice (ff.twice (gg.twice (zz.twice tt))))
  have t i : ⌈budget i⌉₊ = fuel i + 1 := by
    change ⌈(fuel i : ℝ)+1⌉₊ = fuel i+1
    rw [← Nat.cast_add_one, Nat.ceil_natCast]
  have H (i : I) : ⌈budget i⌉₊+1 ≤ 2*(fuel i+1) := by rw [t]; omega
  have cmd := out.bound 2 2 H H
  apply cmd.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro i
  simp only [rulers,space,tail,room_cat,p,f,g,z,send_prod]

theorem prepare {I : Type} (b : I → ℕ) (x : (i : I) → Request (b i))
    (hb : ∀ i, 2 ≤ b i) (valid : ∀ i, Request.Admissible (x i)) :
    BoundedTask (fun i => cost (x i)) (fun i => cost (x i))
      (fun i => .fork (send (tally (b i))) (x i).header) (fun i => send (rulers (x i))) :=
  prepare_solid b x hb fun i =>
    ⟨fun j hj => (valid i j (by simp [hj])).1,
     fun j hj => (valid i j (by simp [hj])).1,
     fun j hj => (valid i j (by simp [hj])).1⟩

end InterchangeROMLeafMasksShape

end NearSquareRoot
end Computability
end OAI
