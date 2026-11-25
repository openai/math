import OAI.Computability.NearSquareRoot.InterchangeROMOuterNative

/-! # Additive growth of the grouped center header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic
  InterchangeROMExpose InterchangeAddress InterchangeFrame

/-- Each extra radix entry is a unary list of at most `b` cells in the
descriptor, costing `2*(b+1)` encoded nodes including the list constructor.
The grouping contributes at most `2*n` entries. -/
def overhead (b n : ℕ) : ℕ := 4 * (b + 1) * n

theorem computable_overhead {X : Type} [Primcodable X] {b n : X → ℕ}
    (hb : Computable b) (hn : Computable n) : Computable (fun x => overhead (b x) (n x)) :=
  Primrec.nat_mul.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (.const 4) (Primrec.succ.to_comp.comp hb)) hn

private theorem shape_cat (p s : Tape) :
    size (shape (p ++ s)) + 1 = size (shape p) + size (shape s) := by
  simpa only [shape,List.map_append] using size_append_right (shape p) (shape s)

private theorem field_size (b t : ℕ) : size (shape (field b t)) = 2 * (b+1) * t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [field,shape_cons,size_cons,size_tally,tally_length,ih]
    ring

/-- Bank grouping retains every incoming spectator and adds only the grouped
prefix digit, the leading digit on the second wing, and two copies of the
short trailing remainder. -/
theorem grouped_header_growth (i : Input) (W : ℕ) (hW : 3 ≤ W) (_hw : W ≤ i.b) :
    size (groupedHeader i W) ≤ i.req.header.count + overhead i.b i.n := by
  let g := BatchRows.groups i.b W
  let t := rem i
  have hg : g ≤ i.b :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < W)).2 (Nat.le_mul_of_pos_left _ (by omega))
  have ht : t+1 ≤ i.n := Request.tail_lt _ i.slots
  have hf : f i ≤ i.req.width :=
    Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  have hbudget := Nat.mul_le_mul_left (4*(i.b+1)) ht
  rw [Nat.mul_add,Nat.mul_one] at hbudget
  have p := shape_cat i.req.before [g]
  have g1 := shape_cat i.req.between (field i.b 1)
  have g2 := shape_cat (field i.b t) (i.req.between ++ field i.b 1)
  have s := shape_cat (field i.b t) i.req.after_
  have sg : size (shape [g]) = 2*(g+1)+1 := by simpa only [Nat.mul_one,field] using field_size g 1
  rw [sg] at p
  rw [field_size] at g1 s g2
  change size (tally (f i), shape (i.req.before ++ [g]),
      shape (field i.b t ++ (i.req.between ++ field i.b 1)),shape (field i.b t ++ i.req.after_)) ≤
    size (tally i.req.width,shape i.req.before,shape i.req.between,shape i.req.after_) + 4*(i.b+1)*i.n
  simp only [size_prod,size_tally,tally_length]
  simp only [Nat.mul_one] at g1
  have double : 4*(i.b+1)*t = 2*(i.b+1)*t + 2*(i.b+1)*t := by ring
  omega

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
