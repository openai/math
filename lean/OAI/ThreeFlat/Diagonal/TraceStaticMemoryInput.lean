import OAI.ThreeFlat.Diagonal.TracePublicMemoryControls
import OAI.ThreeFlat.Diagonal.TraceMemoryPacketInputs

namespace OAI
/-! # A common circuit for the initial memory slots at all physical sites -/

namespace ThreeFlat.Diagonal.TraceRowPackets

open Computability.VPVNP BurstRAM TraceRows TraceSlots TraceWords TraceCompose
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w r S f d : ℕ} {κ σ : Type*}

private def basisWord {b : ℕ} (j : Fin b) : Word b :=
  ⟨2^j.val,Nat.pow_lt_pow_right (by decide : 1 < 2) j.isLt⟩

private theorem bits_basis {b : ℕ} (j : Fin b) : bits (basisWord j) j = true := by
  simp [bits,basisWord]

private theorem bits_zero {b : ℕ} (j : Fin b) : bits (0 : Word b) j = false := by simp [bits]

private def withPublicBit {b : ℕ} {τ : Type*} (j : Fin b) (c : Expr (σ ⊕ τ))
    (e : Word b → Expr σ) : Expr (σ ⊕ τ) :=
  Expr.mux c ((e (basisWord j)).rename Sum.inl) ((e 0).rename Sum.inl)

private theorem withPublicBit_eval {b : ℕ} {τ : Type*} (j : Fin b) (c : Expr (σ ⊕ τ))
    (e : Word b → Expr σ) (x : σ → Bool) (ctrl : τ → Bool) (v : Word b)
    (hc : c.eval (Sum.elim x ctrl) = bits v j)
    (irr : ∀ u, bits u j = bits v j → (e u).eval x = (e v).eval x) :
    (withPublicBit j c e).eval (Sum.elim x ctrl) = (e v).eval x := by
  simp only [withPublicBit, Expr.eval_mux, hc, Expr.eval_rename]
  cases h : bits v j with
  | false => exact irr 0 ((bits_zero j).trans h.symm)
  | true => exact irr (basisWord j) ((bits_basis j).trans h.symm)

private theorem withPublicBit_size {b : ℕ} {τ : Type*} (j : Fin b) (c : Expr (σ ⊕ τ))
    (e : Word b → Expr σ) {u : ℕ} (hc : c.size ≤ 1) (he : ∀ v, (e v).size ≤ u) :
    (withPublicBit j c e).size ≤ 2*u+6 := by
  have h₁ := he (basisWord j)
  have h₀ := he 0
  simp [withPublicBit, Expr.mux, Expr.size]
  omega

private def controlBit (i : InitControl w) : Expr (LocalPort w r d ⊕ (InitControl w ⊕ κ)) :=
  .input (.inr (.inl i))

/-- Header, CPU-probe and empty inputs use the same expression at each row.
All shared-edge fields remain direct input references. -/
noncomputable def staticInput [Fintype κ] (hw : 3 ≤ w+1) :
    TraceMemoryCircuit.Port d (w+1) → Packet (LocalPort w r d ⊕ (InitControl w ⊕ κ))
  | .inl (s,g,j) =>
    let init := withPublicBit j (controlBit (s,.inr (false,j)))
      (fun a => initKey a (headerExpr s) g j)
    let probe := withPublicBit j (controlBit (s,.inr (true,j)))
      (fun t => probeKey hw (cpuExpr s.castSucc) t g j)
    TracePair.formulaPacket (Expr.mux (controlBit (s,.inl false)) init
      (Expr.mux (controlBit (s,.inl true)) probe
        (.const (bits (fields (by omega) (none : TraceSortSite.Narrow (w+1)) g) j))))
  | .inr (.inl (l,b,s,g,j)) =>
    read (.inl (.inr (.inr (.inl (l,b,s,finProdFinEquiv (g,j))))))
  | .inr (.inr (b,g,j)) =>
    read (.inl (.inr (.inr (.inr (b,finProdFinEquiv (g,j))))))

theorem staticInput_eval [Fintype κ] (hw : 3 ≤ w+1) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) (x : LocalPort w r d → Bool) (z : κ → Bool)
    (a : TraceMemoryCircuit.Port d (w+1)) :
    (staticInput hw a).2.eval (Sum.elim x (Sum.elim (initControlAt S f v) z)) =
      (memoryInput hw hs hf v a).2.eval x := by
  rcases a with ⟨s,g,j⟩ | (⟨l,b,s,g,j⟩ | ⟨b,g,j⟩)
  · by_cases h₁ : slotAddress d v s < S
    · simp only [staticInput, TracePair.formulaPacket_eval, Expr.eval_mux, controlBit, Expr.eval,
        Sum.elim_inr, Sum.elim_inl, initControlAt, h₁, decide_true, ite_true, initialInput_eval]
      apply withPublicBit_eval
      · rfl
      · exact fun u => initKey_bit_congr _ _ u _ _ _
    · by_cases h₂ : slotAddress d v s-S < f
      · simp only [staticInput, TracePair.formulaPacket_eval, Expr.eval_mux, controlBit, Expr.eval,
          Sum.elim_inr, Sum.elim_inl, initControlAt, h₁, h₂, decide_false, decide_true, ite_true,
          Bool.false_eq_true, ite_false, initialInput_eval]
        apply withPublicBit_eval
        · rfl
        · exact fun u => probeKey_bit_congr _ _ _ u _ _ _
      · simp only [staticInput, TracePair.formulaPacket_eval, Expr.eval_mux, controlBit, Expr.eval,
          Sum.elim_inr, Sum.elim_inl, initControlAt, h₁, h₂, decide_false, Bool.false_eq_true,
          ite_false, initialInput_eval]; rfl
  · rfl
  · rfl

theorem staticInput_size [Fintype κ] (hw : 3 ≤ w+1) (a : TraceMemoryCircuit.Port d (w+1)) :
    (staticInput (r := r) (κ := κ) hw a).1 ≤ 560*(w+2) := by
  rcases a with ⟨s,g,j⟩ | (⟨l,b,s,g,j⟩ | ⟨b,g,j⟩)
  · apply (TracePair.formulaPacket_size_le _).trans
    let initC := controlBit (r := r) (d := d) (κ := κ) (s,Sum.inr (false,j))
    let timeC := controlBit (r := r) (d := d) (κ := κ) (s,Sum.inr (true,j))
    have hi : (withPublicBit j initC (fun a => initKey a (headerExpr s) g j)).size ≤ 2*1+6 :=
      withPublicBit_size j initC _ (by rfl) (fun a => initKey_size a _
        (fun k => by induction k using Fin.lastCases <;> simp [headerExpr,Expr.size]) _ _)
    have hp : (withPublicBit j timeC (fun t => probeKey hw (cpuExpr s.castSucc) t g j)).size ≤
        2*(56*(w+2))+6 :=
      withPublicBit_size j timeC _ (by rfl) (fun t => probeKey_size hw _ t (fun _ => by rfl) _ _)
    dsimp only [initC,timeC,controlBit] at hi hp
    simp only [Expr.mux, Expr.size, controlBit]
    omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

end ThreeFlat.Diagonal.TraceRowPackets

end OAI
