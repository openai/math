import OAI.Computability.MultitapeWeakETH.MotifFixed

/-! # Assembling a motif argument from its numerical widths and operand ranges -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifSelector MotifBlocks MotifConversion
open MotifGrid PairSimulation LocalHistory Carry Staff Strip
open scoped Classical
noncomputable section

private theorem bank_poly {I X A : Type} [Fintype I] [Codec X] [Codec A]
    (item : I → X → A) (p : ∀ i, Poly (item i)) : Poly (fun x => bank (fun i => item i x)) := by
  have build (n : ℕ) (f : Fin n → X → A) (cost : ∀ i, Poly (f i)) :
      Poly (fun x => List.ofFn (fun i => f i x)) := by
    induction n with
    | zero => simpa using (Code.Poly.const (X:=X) ([] : List A))
    | succ n ih =>
      simp only [List.ofFn_succ]
      exact ((cost 0).pair (ih _ (fun i => cost i.succ))).compose Easy.cons.poly
  exact build _ _ (fun i => p ((Fintype.equivFin I).symm i))

variable {X k J D E : Type} [Codec X] [Field k] [Fintype J] [Fintype D] [Fintype E] [DecidableEq J]
  {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
  (party : X → Label J) (demand : D → X → Tally) (payload : E → X → Tally)
  (readD : Bool × D → X × Tally → Bits.Word) (readS : Bool × E → X × Tally → Bits.Word)

private def endId {A B : Type} {src dst : A → B} {j : B} : Ends src dst j → Bool × A
  | .inl e => (false,e.val)
  | .inr e => (true,e.val)

private def demandBank (j : J) (x : X) := bank fun e : Ends a b j =>
  readD (endId e) (x,demand (endId e).2 x)

private def full (e : E) (x : X) := payload e x ++
  tally (repetitions B (fun d => (demand d x).length)*B.selectorBits)

private def supplyBank (j : J) (x : X) := bank fun e : Port P j =>
  (readS (endId e) (x,full B demand payload (endId e).2 x),payload (endId e).2 x)

def bufferInput (x : X) : FixedInput J :=
  (((bank (fun d => demand d x),party x),demandBank (a:=a) (b:=b) demand readD (party x).val x),
    supplyBank B demand payload readS (party x).val x,bank (fun e => payload e x))

variable (pp : Poly party) (dp : ∀ e, Poly (demand e)) (sp : ∀ e, Poly (payload e))
  (dr : ∀ e, Poly (readD e)) (sr : ∀ e, Poly (readS e))

include pp dp sp dr sr in
theorem bufferInput_poly : Poly (bufferInput B party demand payload readD readS) := by
  have dw := bank_poly demand dp
  have copies := dw.compose (copies_poly p B.scale)
  have r : Poly (fun x => tally (repetitions B (fun d => (demand d x).length))) := by
    convert copies using 1
    funext x
    congr 2
    funext e
    simp only [raw,fetch_bank]
  let reg : Regime X := ⟨size,send,Dom.base _⟩
  have r' : Realizes reg (fun x => repetitions B (fun d => (demand d x).length)) := r
  have extent (e : E) : Poly (full B demand payload e) := (sp e).app (r'.times (Realizes.fix B.selectorBits))
  have ds (j : J) : Poly (demandBank (a:=a) (b:=b) demand readD j) := bank_poly _ fun e =>
    (Poly.identity.pair (dp (endId e).2)).compose (dr (endId e))
  have ss (j : J) : Poly (supplyBank B demand payload readS j) := bank_poly _ fun e =>
    (((Poly.identity.pair (extent (endId e).2)).compose (sr (endId e))).pair (sp (endId e).2))
  exact (((dw.pair pp).pair (select_poly party pp _ ds _ (Code.Poly.const []))).pair
    ((select_poly party pp _ ss _ (Code.Poly.const [])).pair (bank_poly payload sp)))

omit [Codec X] in
/-- The readback contract for each incident operand includes all selector bits above
the supply payload. The same input format accommodates refresh and shrinking. -/
theorem bufferInput_eq (x : X) (I : EntryInput B) (pj : party x = ⟨I.party⟩)
    (width : ∀ e, demand e x = tally (I.demand e)) (pay : ∀ e, payload e x = tally (I.payload e))
    (outD : ∀ e (h : I.party=a e), readD (false,e) (x,tally (I.demand e)) =
      List.ofFn (MotifEntry.inputBits (I.demandBits.1 e h)))
    (inD : ∀ e (h : I.party=b e), readD (true,e) (x,tally (I.demand e)) =
      List.ofFn (MotifEntry.inputBits (I.demandBits.2 e h)))
    (outS : ∀ e (h : I.party=P.src e), readS (false,e) (x,tally (supplyWidths B I.demand I.payload e)) =
      List.ofFn (MotifEntry.inputBits (I.supplyBits.1 e h)))
    (inS : ∀ e (h : I.party=P.dst e), readS (true,e) (x,tally (supplyWidths B I.demand I.payload e)) =
      List.ofFn (MotifEntry.inputBits (I.supplyBits.2 e h))) :
    bufferInput B party demand payload readD readS x = fixedInput B I := by
  have extEq (e : E) : full B demand payload e x = tally (supplyWidths B I.demand I.payload e) := by
    simp only [full,pay,width,tally_length]
    rw [← recover_tally (_ ++ _)]
    simp only [List.length_append,tally_length]
    rfl
  unfold bufferInput
  rw [pj]
  simp only [fixedInput,mapInput,supplyInput,demandBank,supplyBank,width,pay,extEq]
  congr 2
  · apply congrArg (bank (I:=Ends a b I.party) (A:=Bits.Word))
    funext e
    cases e with
    | inl e => exact outD e.val e.prop
    | inr e => exact inD e.val e.prop
  · apply congrArg (bank (I:=Port P I.party) (A:=Bits.Word × Tally))
    funext e
    cases e with
    | inl e => exact Prod.ext (outS e.val e.prop) rfl
    | inr e => exact Prod.ext (inS e.val e.prop) rfl

end
end OAI.Computability.MultitapeWeakETH.MotifFields
