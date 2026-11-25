import OAI.Computability.IntegerMultiplication.Lea.Pose

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Param Scale Dune Cone Halo Echo Code Strip Brief Carry Staff Bureau Cap
variable {n:ℕ}(h:Season n)
abbrev boxes n:= Cap.space (Echo.modulus n)
include h
theorem boxes_lt: boxes n≤load n:=by
  rw [← h.volume]
  exact Finset.prod_le_prod (f:=modulus n) (g:=criterion n) (fun j _=>pitch h j)
omit h in
theorem widthX :
    n ≤ ton (fun (_:Unit)=>n) () :=
  (budget_times n).trans (by
    unfold ton Scale.P; rw [mul_comm]; gcongr; change Param.amount n ≤ load n;have h:= load_above n; omega)
theorem enough_x : n≤ boxes n*Scale.P n :=
  (budget_times n).trans (by rw [mul_comm]; apply Nat.mul_le_mul_right _; have h:2*Param.amount n≤ boxes n:= h.enoughBits; omega)

variable {I:Type}{r:Regime I}(n:I→ℕ)(g:Guide r n)
omit h
include g
theorem boxes_cook :
    Figure r (boxes ∘ n):= by
  unfold boxes Cap.space
  let d:= lanes ∘ n
  let k:=g.spread n
  exact (Cap.lists d k (fun i j=>moduli (n i) j.val)
    ((g.abroad n k).size_ (n ∘ (Sigma.fst:Across d→I)) (floor_ d k))).1
omit g

variable (v:∀i,Season (n i))
include v
abbrev tagK:=boxes ∘ n
abbrev budgetK:= Scale.P ∘ n
abbrev tokenP (a:I→ℕ) i:=send (Code.tally (a i))
private theorem tag_w i:tagK n i ≤ton n i:= (boxes_lt (v i)).trans (Nat.le_mul_of_pos_right _ (budget_p _))
private theorem tagN :
    Carries (token n) (cell n) (tokenP (tagK n)):= dispatchT _ (boxes_cook n (guide_city n)) (tag_w n v)
omit v in
theorem tagP :
    Carries (token n) (cell n) (tokenP (budgetK n)):=
  Bureau.dispatch ((guide_city n).fund n)
abbrev LongPx(i:I):= tagK n i * budgetK n i
theorem periodT :
    Carries (token n) (cell n) (tokenP (LongPx n)) :=
  let g:=guide_city n
  dispatchT _ ((boxes_cook n g).multiplied (Figure.of_spoken (g.fund n))) (fun i=>Nat.mul_le_mul_right _ (boxes_lt (v i)))

abbrev stripT (p:I→ℕ)(i:I):=send (List.replicate (tagK n i) (Code.tally (p i)))
theorem planT (p:I→ℕ)(a:Carries (token n) (cell n) (tokenP p))
    (q:ℕ) (e:∀i,p i≤q*Scale.P (n i)):
    Carries (token n) (cell n) (stripT n p):= by
  let b:= tagK n
  let s i:= Series.natural (b i)
  have V:
      Carries (token n) (cell n) (stackRun s (fun i _=>send (Code.tally (p i)))) := by
    apply Strip.spread
    · unfold s; simp only [Series.count_natural]; exact (tagN n v).twice a
    refine ⟨5*q+2,fun i=>?_⟩
    unfold s
    change _ *(size (Code.tally (p i)):ℝ) ≤_
    rw [size_tally,tally_length,Series.count_natural]
    unfold token ton; norm_cast
    have V:=boxes_lt (v i)
    have Q:=budget_p (n i)
    have Y:1≤load (n i):=Nat.pow_pos (by decide)
    have M:(b i+1)*(2*p i+1)≤ (load (n i)+1)*(2*(q*(P (n i)))+1):= Nat.mul_le_mul
      (Nat.add_le_add_right V 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (e i)) 1)
    exact M.trans (by unfold Scale.P at *; nlinarith [Nat.mul_le_mul_right (q*budget (n i)) Y,Nat.le_mul_of_pos_right (load (n i)) Q])
  have L i:(stackRun s (fun i _=>send (Code.tally (p i)))) i=stripT n p i:=by
    unfold stackRun s stripT
    rw [stripe_eq' _ (fun _=>Code.tally _),Series.tab]; congr 1
    change (List.finRange _).map _=_
    simp [List.map_const',b]
  rw [← funext L]; exact V

omit v in
theorem sizeInput (x:I→Bits.Word)(a:∀ i,(x i).length=n i):
    close n (send ∘ x):= by
  refine ⟨3,fun i=>?_⟩
  change (Code.size (x i):ℝ)≤ _
  rw [Bits.size_word,a]
  unfold token
  norm_cast
  have V: n i≤ton n i:=widthX (n:=n i); have H:=tonp n i; omega
end Lea

end IntegerMultiplication
end Computability
end OAI
