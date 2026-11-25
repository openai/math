import OAI.Computability.MultitapeWeakETH.InitialIncidence
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Uniform bit programs for all six initial graph columns -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence

open IntegerMultiplication Code Bits Carry Staff Strip
open scoped Classical
noncomputable section

private def xorWords (q : Word × Word) := (zipSafe false false q).map (fun p => p.1 ^^ p.2)

private theorem xorWords_poly : Poly xorWords :=
  (easy_zipSafe false false Easy.identity).poly.compose
    (Poly.maps _ (Easy.finite (fun p : Bool × Bool => p.1 ^^ p.2)).poly)

private theorem xorValue (x y : Word) : value (xorWords (x,y)) = value x ^^^ value y := by
  have eq (a b : Word) (len : a.length=b.length) :
      value ((a.zip b).map fun p => p.1 ^^ p.2) = value a ^^^ value b := by
    induction a generalizing b with
    | nil => cases b <;> simp_all
    | cons c a ih =>
      cases b with
      | nil => simp at len
      | cons e b =>
        have tail := ih b (by simpa using len)
        change digit (c ^^ e)+2*value ((a.zip b).map fun t => t.1 ^^ t.2) = (digit c+2*value a) ^^^ (digit e+2*value b)
        rw [tail]
        have step (b : Bool) (n : ℕ) : digit b+2*n = Nat.bit b n := by cases b <;> simp [Nat.bit_val,Nat.add_comm]
        simp only [step]
        apply Nat.eq_of_testBit_eq
        intro j
        cases j <;> simp only [Nat.testBit_xor,Nat.testBit_bit_zero,Nat.testBit_bit_succ]
  have := eq (x++List.replicate y.length false) (y++List.replicate x.length false) (by simp [Nat.add_comm])
  simpa only [xorWords,zipSafe,value_append,zeroes,mul_zero,add_zero] using this

private theorem xorFigure {I : Type} {reg : Regime I} {f g : I → ℕ} (a : Figure reg f) (b : Figure reg g) :
    Figure reg (fun i => f i ^^^ g i) := a.lift2 b xorWords_poly xorValue

private theorem chooseEq {I : Type} {reg : Regime I} {f g x y : I → ℕ} (a : Figure reg f) (b : Figure reg g)
    (u : Figure reg x) (v : Figure reg y) : Figure reg (fun i => if f i = g i then x i else y i) := by
  have H := v.variant (v.variant u (b.compare_ a)) (a.compare_ b)
  convert H using 1
  funext i
  rcases lt_trichotomy (f i) (g i) with lt | eq | gt
  · simp [lt,ne_of_lt lt]
  · simp [eq]
  · simp [not_lt_of_gt gt,gt,ne_of_gt gt]

/-- Unary lane and offset exponents, followed by the binary row index. -/
abbrev Query := Tally × Tally × Word
private abbrev reg : Regime Query := ⟨size,send,Dom.base _⟩

/-- The program returns the numerical contents of a cell without materializing
a tensor or searching the full payload space. Its time is polynomial in the
unary parameters and the binary row length, also on malformed inputs. -/
theorem column_program (a : ℕ) (c : Fin 6) :
    ∃ read : Query → Word, Poly read ∧ ∀ q,
      value (read q) = column a q.1.length q.2.1.length c (value q.2.2) := by
  have g : Realizes reg (fun q => q.1.length) := by
    change Poly (fun q : Query => tally q.1.length)
    simpa only [recover_tally] using (Easy.fst (X:=Tally) (Y:=Tally × Word)).poly
  have r : Realizes reg (fun q => q.2.1.length) := by
    change Poly (fun q : Query => tally q.2.1.length)
    simpa only [recover_tally] using (Easy.snd (X:=Tally) |>.compose (Easy.fst (Y:=Word))).poly
  have row : Figure reg (fun q => value q.2.2) := ⟨_,(Easy.snd.compose Easy.snd).poly,fun _ => rfl⟩
  let zero := Figure.natural (r:=reg) 0
  let one := Figure.natural (r:=reg) 1
  let two := Figure.natural (r:=reg) 2
  let D := Figure.natural (r:=reg) (2^a)
  let V := two.repeated g
  let depth := g.plus (r.plus (Realizes.fix 2))
  let d := Figure.of_spoken depth
  let i := row.quotients D
  let p := row.modded D
  let base := i.quotients V
  let x := i.modded V
  have nxt {z : Query → ℕ} (h : Figure reg z) : Figure reg (fun t => nextStage (t.1.length+(t.2.1.length+2)) (z t)) :=
    chooseEq (h.added one) (two.multiplied d) zero (h.added one)
  have prev {z : Query → ℕ} (h : Figure reg z) : Figure reg (fun t => prevStage (t.1.length+(t.2.1.length+2)) (z t)) :=
    chooseEq h zero ((two.multiplied d).subtracted one) (h.subtracted one)
  have axisF {z : Query → ℕ} (h : Figure reg z) : Figure reg (fun t => axis (t.1.length+(t.2.1.length+2)) (z t)) :=
    h.variant (((two.multiplied d).subtracted one).subtracted h) (h.compare_ d)
  have maskF {z : Query → ℕ} (h : Figure reg z) :
      Figure reg (fun t => mask t.1.length (z t) (value t.2.2%2^a)) := by
    let power := ((Figure.of_spoken (g.minused (Realizes.fix 1))).subtracted h)
    have bound := (diameter _ g).mono fun q => (Nat.sub_le (q.1.length-1) (z q)).trans (Nat.sub_le _ _)
    have H := chooseEq p one ((two.repeated (power.pay bound)).variant zero (h.compare_ (Figure.of_spoken g))) zero
    convert H using 1
    funext t
    dsimp only [mask]
    split_ifs <;> simp_all
  change Figure reg _
  fin_cases c
  · exact ((nxt i).multiplied D).added p
  · exact ((prev i).multiplied D).added p
  · exact maskF (axisF i)
  · exact ((((nxt base).multiplied V).added (xorFigure x (maskF (axisF base)))).multiplied D).added p
  · exact ((((prev base).multiplied V).added (xorFigure x (maskF (axisF (prev base))))).multiplied D).added p
  · exact (two.repeated (r.plus (Realizes.fix 2))).variant zero (p.compare_ two)

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
