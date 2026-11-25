import OAI.ThreeFlat.Diagonal.TraceStaticRow

namespace OAI
/-! # Evaluating the public row controls recovers the physical trace verifier -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM TraceWords TraceRows TraceBanks TraceCompose
open TraceRowPackets TraceProgram TraceUniformRow
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

private theorem literal_at {a : Type*} (b : Bool) (x : a → Bool) : (literal b).2.eval x=b := rfl
private theorem read_at {a : Type*} (j : a) (x : a → Bool) : (TraceRowPackets.read j).2.eval x=x j := rfl
private theorem if_eval {a : Type*} (q : Prop) [Decidable q] (yes no : Packet a) (x : a → Bool) :
    (if q then yes else no).2.eval x=if q then yes.2.eval x else no.2.eval x := by
  by_cases h : q
  · exact (congrArg (fun t : Packet a => t.2.eval x) (ite_eq_left h)).trans (ite_eq_left h).symm
  · exact (congrArg (fun t : Packet a => t.2.eval x) (ite_eq_right h)).trans (ite_eq_right h).symm

theorem template_eval (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (a : Check F w p k) (x : TraceUniformRow.Port w p r k d → Bool) :
    ((template (d:=d) hF hw hp base f st a).2.eval (Sum.elim x (ctrlAt hw hs hf base v))) =
      (check hF hw hp hp0 base st hs hf v a).2.eval x := by
  have hmem : (Sum.elim x (ctrlAt hw hs hf base v)) ∘ memoryPort =
    Sum.elim (x ∘ Sum.inl) (memoryControlAt hw hs hf v) := by
    funext a; cases a <;> rfl
  rcases a with ((u|⟨s,j|i⟩)|(u|⟨j,b⟩))
  · cases u
    rw [template,liftPort_eval,hmem,staticMemory_eval]
    symm; apply ordinary_eval
  · fin_cases j
    · change (select (flag (.inl s)) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
        (ordinary (if decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f) then _ else _)).2.eval x
      by_cases active : S ≤ slotAddress d v s ∧ slotAddress d v s-S<f <;>
        simp only [select_eval,flag_at,outerAt,ordinary_eval,if_eval,active,decide_false,
          eq_self,ite_false,Bool.false_eq_true,substituteFintype_eval,read_at,literal_at]; rfl
    · change (select (flag (.inl s)) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
        (if S ≤ slotAddress d v s ∧ slotAddress d v s-S<f then _ else _ : Packet (TraceUniformRow.Port w p r k d)).2.eval x
      by_cases active : S ≤ slotAddress d v s ∧ slotAddress d v s-S<f <;>
        simp only [select_eval,flag_at,outerAt,if_eval,active,decide_false,
          eq_self,ite_false,Bool.false_eq_true,liftPort_eval,literal_at]; rfl
    · change (select (flag (.inr (.inl s))) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
        (if slotAddress d v s=S ∧ 0<f then _ else _ : Packet (TraceUniformRow.Port w p r k d)).2.eval x
      by_cases first : slotAddress d v s=S ∧ 0<f <;>
        simp only [select_eval,flag_at,outerAt,if_eval,first,decide_true,decide_false,
          eq_self,ite_false,Bool.false_eq_true,liftPort_eval,literal_at]; rfl
  · change (select (flag (.inl s)) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
      (ordinary (if decide (S ≤ slotAddress d v s ∧ slotAddress d v s-S<f) then _ else _)).2.eval x
    by_cases active : S ≤ slotAddress d v s ∧ slotAddress d v s-S<f <;>
      simp only [select_eval,flag_at,outerAt,ordinary_eval,if_eval,active,decide_false,
        eq_self,ite_false,Bool.false_eq_true,substituteFintype_eval,read_at,literal_at]; rfl
  · cases u
    change (select (flag (.inr (.inr (.inl false)))) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
      (if v.val=0 then _ else _ : Packet (TraceUniformRow.Port w p r k d)).2.eval x
    by_cases first : v.val=0 <;>
      simp only [select_eval,flag_at,outerAt,if_eval,first,decide_true,decide_false,
        eq_self,ite_true,ite_false,Bool.false_eq_true,liftPort_eval,substituteFintype_eval,read_at,literal_at]; rfl
  · cases b with
    | false =>
      change (select (flag (.inr (.inr (.inr j)))) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
        (if (base+(finProdFinEquiv j).val)/2=v.val then _ else _ : Packet (TraceUniformRow.Port w p r k d)).2.eval x
      by_cases own : (base+(finProdFinEquiv j).val)/2=v.val <;>
        simp only [select_eval,flag_at,outerAt,if_eval,own,decide_true,decide_false,
          eq_self,ite_true,ite_false,Bool.false_eq_true,TracePair.formulaPacket_eval,same,literal_at]; rfl
    | true =>
      change (select (flag (.inr (.inr (.inl true)))) _ _).2.eval (Sum.elim x (ctrlAt hw hs hf base v)) =
        (if v.val+1<2^d then _ else _ : Packet (TraceUniformRow.Port w p r k d)).2.eval x
      by_cases successor : v.val+1<2^d <;>
        simp only [select_eval,flag_at,outerAt,if_eval,successor,decide_true,decide_false,
          eq_self,ite_true,ite_false,Bool.false_eq_true,TracePair.formulaPacket_eval,same,literal_at]; rfl

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
