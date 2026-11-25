import OAI.ThreeFlat.Diagonal.TraceUniformCircuit

namespace OAI
/-! # Gate count of the program-independent two-row checker -/

namespace ThreeFlat.Diagonal.TraceProgram

open TraceWords TracePair TraceIssue RAM
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

def shapeBudget (p r k : ℕ) := 15*(p+r+k+10)^5
def pinBudget (w p r k : ℕ) := 2*((5+r)*(w+1)) + (1+6*p+k)*w + p*shapeBudget p r k
def slotBudget (w p r k : ℕ) := shapeBudget p r k*(6*(10*w+2)+4)+1
def controlBudget (w p r k : ℕ) :=
  let word := 10*(w+1)+1
  3*word + (p*(word+slotBudget w p r k+2)+1) + 4

theorem card_shape (p r k : ℕ) : Fintype.card (Instr 0 p r k) ≤ shapeBudget p r k := by
  have hs : Function.Surjective (InstructionShapes.all p r k).get := fun z =>
    List.mem_iff_get.mp (InstructionShapes.mem_all z)
  have hc := Fintype.card_le_of_surjective (InstructionShapes.all p r k).get hs
  rw [Fintype.card_fin] at hc
  exact hc.trans (InstructionShapes.all_length_le p r k)

theorem card_control (w p r k : ℕ) : Fintype.card (Control w p r k) ≤ pinBudget w p r k := by
  have hc := Nat.mul_le_mul_left p (card_shape p r k)
  simpa [Control,Input,Raw,Text,pinBudget,Nat.mul_assoc] using
    Nat.add_le_add_left hc (2*((5+r)*(w+1))+(1+6*p+k)*w)

theorem control_size (w p r k : ℕ) : (control (w:=w) (p:=p) (r:=r) (k:=k)).size ≤ controlBudget w p r k := by
  have hw (side : Bool) (col : Fin 5) (n : Word (w+1)) :
      (rowControl (p:=p) (k:=k) (wordIs (r:=r) side col n)).size ≤ 10*(w+1)+1 := by
    simpa only [rowControl,Expr.size_rename,wordIs,Nat.mul_comm] using
      sameWord_size_le (headerWire (r:=r) side col) (fun j => .const (bits n j)) (fun _ => le_rfl) (fun _ => le_rfl)
  have hs (i : Fin p) : (slot (w:=w) (r:=r) (k:=k) i).size ≤ slotBudget w p r k := by
    exact selectSlot_size _ _ (fun _ _ => le_rfl) (s:=1) (fun _ => le_rfl)
  have hf := TraceFetch.fetch_size_le (fun i => rowControl (p:=p) (r:=r) (k:=k) (pcIs false i))
    (slot (w:=w) (r:=r) (k:=k)) (fun i => hw false 1 _) hs
  have ht (b : Bool) : (rowControl (p:=p) (k:=k) (tagIs (w:=w) (r:=r) b 0)).size ≤ 10*(w+1)+1 := hw b 0 _
  have := ht false
  have := ht true
  simp only [control,Expr.mux,Expr.size,controlBudget]
  omega

private theorem packet_size {b : ℕ} (hb : ∀ (M : Machine w p r k) a, (packet M a).1 ≤ b)
    (i : Fin p) (z : Instr 0 p r k) (a : Port w p r ⊕ Bool) : (candidatePacket i z a).1 ≤ b := by
  cases a with
  | inr b => simpa [candidatePacket] using hb (single i z 0 (fun _ => 0)) (.inr b)
  | inl a =>
    cases a with
    | alu q j =>
      cases z <;> first
        | exact Nat.zero_le _
        | apply (liftPacket_size _).le.trans; apply hb
    | _ => apply (liftPacket_size _).le.trans; apply hb

theorem candidate_size {b f c : ℕ}
    (hb : ∀ (M : Machine w p r k) a, (packet M a).1 ≤ b)
    (hf : ∀ M : Machine w p r k, (formulaPacket (checkExpr M)).1 ≤ f)
    (hc : Fintype.card (Port w p r ⊕ Bool) ≤ c) (i : Fin p) (z : Instr 0 p r k) :
    (candidateCircuit (w:=w) i z).1 ≤ c*b+f := by
  rw [candidateCircuit, TraceCompose.substituteFintype_size]
  apply Nat.add_le_add _ (hf _)
  have hs : (∑ a : Port w p r ⊕ Bool, (candidatePacket i z a).1) ≤ Fintype.card (Port w p r ⊕ Bool)*b := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun a _ => packet_size hb i z a)
  exact hs.trans (Nat.mul_le_mul_right b hc)

theorem uniformPair_size_of {b f c : ℕ}
    (hb : ∀ (M : Machine w p r k) a, (packet M a).1 ≤ b)
    (hf : ∀ M : Machine w p r k, (formulaPacket (checkExpr M)).1 ≤ f)
    (hc : Fintype.card (Port w p r ⊕ Bool) ≤ c) :
    (uniformPair (w:=w) (p:=p) (r:=r) (k:=k)).1 ≤ pinBudget w p r k*(c*b+f)+4*controlBudget w p r k := by
  rw [uniformPair,TraceCompose.substituteFintype_size]
  apply Nat.add_le_add _ ((formulaPacket_size_le _).trans (Nat.mul_le_mul_left _ (control_size ..)))
  have hs (a : Control w p r k) : (source a).1 ≤ c*b+f := by
    rcases a with a|⟨i,z⟩
    · exact Nat.zero_le _
    · exact candidate_size hb hf hc i z
  have hsum : (∑ a : Control w p r k, (source a).1) ≤ Fintype.card (Control w p r k)*(c*b+f) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.univ) (fun a _ => hs a)
  exact hsum.trans (Nat.mul_le_mul_right (c*b+f) (card_control w p r k))

end ThreeFlat.Diagonal.TraceProgram

end OAI
