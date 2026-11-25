import OAI.Computability.BorderVNP.PackedInheritedFields
import OAI.Computability.BorderVNP.PackedLookup

/-! # Batched final relocation of frozen public site words

The two tag bits select the site's bit prefix, its merged box ordinal, or zero.
One checked binary addition writes the final ABI word. Stable named-site lookups
supply both prefixes even when many stored rows belong to the same moved site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Word ParseBatchSort VPVNP.VerifierNetwork PackedHistogram
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

/-- Fixed binary tag representation for a frozen site word. -/
def Kind.flag (k : Kind) (bit : Bool) : Bool :=
  match k, bit with
  | .bitAddress,false | .boxID,true => true
  | _,_ => false

/-- The three word inputs followed by the two relocation flags. -/
abbrev RelocInput (w : ℕ) := (Fin 3 × Fin w) ⊕ Bool

private def pick {w : ℕ} (j : Fin w ⊕ Fin w) : Expr (RelocInput w) :=
  match j with
  | .inl i => .input (.inl (0,i))
  | .inr i => mux (.input (.inr false)) (.input (.inl (1,i)))
      (mux (.input (.inr true)) (.input (.inl (2,i))) (.const false))

/-- Local relocation circuit, without any inspection of the original one-copy tables. -/
noncomputable def relocFrame (w : ℕ) : Frame (RelocInput w) (Fin w) :=
  let flags := (Frame.initial (id : RelocInput w → _)).step pick
  let words := flags.select (fun i : Bool × Fin w => if i.1 then .inr i.2 else .inl i.2)
  (WidthExpr.frame w (.binary .add (.field false) (.field true))).subst words

private theorem zero_value {w : ℕ} : value (fun _ : Fin w => false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa only [value,Bool.toNat_false,zero_mul,zero_add] using ih

/-- Execution returns the designated relocated word and respects leading zeroes. -/
theorem relocFrame_value (w : ℕ) (x : RelocInput w → Bool) (k : Kind) (tag : ∀ b, x (.inr b) = k.flag b)
    (fit : k.move (value (fun j => x (.inl (1,j)))) (value (fun j => x (.inl (2,j))))
      (value (fun j => x (.inl (0,j)))) < 2^w) :
    value ((relocFrame w).eval x) =
      k.move (value (fun j => x (.inl (1,j)))) (value (fun j => x (.inl (2,j))))
        (value (fun j => x (.inl (0,j)))) := by
  let initial := (Frame.initial (id : RelocInput w → _)).step pick
  let words := initial.select (fun i : Bool × Fin w => if i.1 then .inr i.2 else .inl i.2)
  let a (b : Bool) := value (fun j => words.eval x (b,j))
  let expr : WidthExpr Bool := .binary .add (.field false) (.field true)
  have hd : a true + a false = k.move (value (fun j => x (.inl (1,j)))) (value (fun j => x (.inl (2,j))))
        (value (fun j => x (.inl (0,j)))) := by
    cases k <;> simp [a,words,initial,pick,StatementCircuit.Expr.eval,mux_eval,tag,Kind.flag,Kind.move,zero_value]
  have hfits : expr.Fits w a := ⟨value_lt _,value_lt _,by change a false + a true < 2^w; rw [Nat.add_comm,hd]; exact fit⟩
  have hw : (relocFrame w).eval x = (expr.frame w).eval (words.eval x) :=
    funext fun i => Frame.subst_eval _ _ _ _
  rw [hw, expr.frame_value w _ hfits]
  exact (Nat.add_comm _ _).trans hd

/-- Relocating one word costs a quadratic number of elementary gates. -/
theorem relocFrame_size (w : ℕ) : (relocFrame w).size ≤ 400*(w+1)^2 := by
  let flags := (Frame.initial (id : RelocInput w → _)).step pick
  have hp (j : Fin w ⊕ Fin w) : (pick j).size ≤ 20 := by
    cases j <;> simp [pick,mux,StatementCircuit.Expr.size]
  have hs := Frame.step_size_le (Frame.initial (id : RelocInput w → _)) pick 20 hp
  have ha := (WidthExpr.binary .add (.field false) (.field true)).frame_size w
  simp only [Frame.initial_size,Fintype.card_sum,Fintype.card_fin,zero_add] at hs
  simp only [WidthExpr.nodes] at ha
  simp only [relocFrame,Frame.subst_size,Frame.select_size]
  nlinarith

/-- Read both true site prefixes, relocate each marked word and preserve its row position.
The two lookup circuits and the local arithmetic have explicit finite gate counts. -/
theorem exists_relocatedWords {S Q σ : Type*} [Fintype S] [Fintype Q] [Fintype σ] {k w : ℕ}
    (index : S ↪ Fin (2^k)) (owner : Q → Fin k → σ) (payload : Q → Fin w → σ) (tag : Q → Bool → σ)
    (siteOffset boxOffset : S → Fin w → σ) :
    let lookup := fun (offset : S → Fin w → σ) =>
      PackedLookup.lookup (layout S Q) index (fun s i => .input (offset s i)) (fun q j => .input (owner q j))
    ∃ f : Frame σ (Q × Fin w),
      f.size ≤ (lookup siteOffset).size + (lookup boxOffset).size + 1 + Fintype.card Q*(400*(w+1)^2) ∧
      ∀ (x : σ → Bool) (q : Q) (s : S) (kind : Kind),
        value (x ∘ owner q) = (index s).val → (∀ b, x (tag q b) = kind.flag b) →
        let moved := kind.move (value (x ∘ siteOffset s)) (value (x ∘ boxOffset s)) (value (x ∘ payload q))
        moved < 2^w → value (fun j => f.eval x (q,j)) = moved := by
  intro lookup
  let both := Crossing.parallelFrame (lookup siteOffset) (lookup boxOffset)
  let pins (q : Q) : RelocInput w → σ ⊕ ((Q × Fin w) ⊕ (Q × Fin w))
    | .inl (f,i) => ![Sum.inl (payload q i),Sum.inr (.inl (q,i)),Sum.inr (.inr (q,i))] f
    | .inr b => .inl (tag q b)
  let one (q : Q) := (relocFrame w).subst (Frame.initial (pins q))
  obtain ⟨joint,hj,he⟩ := Crossing.exists_parallelFrames one
  let result := (joint.select fun i : Q × Fin w => ⟨i.1,i.2⟩).subst both.withInput
  refine ⟨result,?_,?_⟩
  · have hl (q : Q) : (one q).size ≤ 400*(w+1)^2 := by simpa [one] using relocFrame_size w
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun q _ => hl q)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at hsum
    simp only [result,Frame.subst_size,Frame.select_size,Frame.withInput_size,both,Crossing.parallelFrame_size]
    omega
  · intro x q s kind howner htag moved hfit
    let z := (Frame.initial (pins q)).eval (both.withInput.eval x)
    have hv (offset : S → Fin w → σ) : value (fun j => (lookup offset).eval x (q,j)) = value (x ∘ offset s) :=
      PackedLookup.lookup_value _ _ _ _ _ _ _ howner
    have hs : value (fun j => z (.inl (1,j))) = value (x ∘ siteOffset s) := by
      simpa [z,pins,both] using hv siteOffset
    have hb : value (fun j => z (.inl (2,j))) = value (x ∘ boxOffset s) := by
      simpa [z,pins,both] using hv boxOffset
    have hp : value (fun j => z (.inl (0,j))) = value (x ∘ payload q) := by simp [z,pins,Function.comp_def]
    have ht (b : Bool) : z (.inr b) = kind.flag b := by simpa [z,pins] using htag b
    have hfit' : kind.move (value (fun j => z (.inl (1,j)))) (value (fun j => z (.inl (2,j))))
      (value (fun j => z (.inl (0,j)))) < 2^w := by rwa [hs,hb,hp]
    have out : (fun j => result.eval x (q,j)) = (relocFrame w).eval z := by
      funext j
      simp [result,he,one,z]
    rw [out,relocFrame_value w z kind ht hfit',hs,hb,hp]

end Packing.Inherited

end BorderVNP
end Computability
end OAI
