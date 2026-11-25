import OAI.Computability.BorderVNP.PackedDescriptorInputs

/-! # Boolean interval clipping on the physical sparse cable table

On an occupied charged cable, all inputs come from actual sort-and-scan circuits. On an
uncharged cable the same fragment uses its full-width tail. Virtual holes can contain
arbitrary old words. They impose no predicate on the other rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CutCircuit

open Crossing Shortening Shortening.SeedIntervals ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin
open scoped Classical

private abbrev Stage (σ : Type*) (D M w : ℕ) := σ ⊕ ((Fin M × Fin w) ⊕ (Fin M × (Band D × Bool) × Fin w))

private def inputFormula {σ : Type*} {D M k w : ℕ} (p : PublicPopulation.Pins (Fin M) σ k w)
    (z : (Fin M × Band D) × Input × Fin w) : Expr (Stage σ D M w) :=
  let u := z.1.1
  let b := z.1.2
  let j := z.2.2
  let width := StatementCircuit.Expr.input (.inl (p.width u j))
  let active := StatementCircuit.Expr.input (.inl (p.active u))
  match z.2.1 with
  | .width => width
  | .start => .and active (.input (.inr (.inl (u,j))))
  | .lo => .and active (.input (.inr (.inr (u,(b,false),j))))
  | .hi => mux active (.input (.inr (.inr (u,(b,true),j))))
      (if b.isNone then width else .const false)

private theorem formula_size {σ : Type*} {D M k w : ℕ} (p : PublicPopulation.Pins (Fin M) σ k w)
    (z : (Fin M × Band D) × Input × Fin w) : (inputFormula p z).size ≤ 12 := by
  rcases z with ⟨⟨u,b⟩, f,j⟩
  cases f <;> cases b <;> simp [inputFormula,mux,StatementCircuit.Expr.size]

private theorem zeroValue (w : ℕ) : value (fun _ : Fin w => false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [value,ih]

/-- One computed layout of all old band starts, spans and matched ordinals. The same layout
works for every geometric network represented by the raw words and any previous history. -/
theorem live_cut_frames (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C e : ℕ, ∀ (M k w : ℕ) {A : Type} {σ : Type*} [Fintype A] [Fintype σ]
      (p : PublicPopulation.Pins (Fin M) σ k w) (code : A ↪ Fin (2^k)) (perm : Fin D → Equiv.Perm A),
      ∃ f : Frame σ ((Fin M × Band D) × Result × Fin w),
        f.size ≤ (PublicPopulation.offsets p).size +
          PoolCircuit.scatterCost (Fintype.card A) M D C e k w +
          M*Fintype.card (Band D)*(48*w) + 1 + M*Fintype.card (Band D)*(3300*(w+1)^2) ∧
        ∀ {P : Type*} {bits : P → ℕ} (N : Network D P bits) (bin : N.Edge → Option A)
          (slot : N.Edge ↪ Fin M) (x : σ → Bool),
          PublicPopulation.Represents p N bin slot code x → (∀ a, count N bin a < 2^w) →
          (∀ c, value (x ∘ p.width (slot c)) = N.width c) →
          ∀ c b r, value (fun j => f.eval x ((slot c,b),r,j)) =
            r.read (liveDescriptor N slot bin perm m (fun a => (code a).val) c b) := by
  obtain ⟨C,e,sc⟩ := PoolCircuit.scatter_frames D m hm
  refine ⟨C,e,fun M k w A σ _ _ p code perm => ?_⟩
  obtain ⟨bounds,hb,eb⟩ := sc k w p code perm
  let joined := parallelFrame (Frame.initial (id : σ → σ)) (parallelFrame (PublicPopulation.offsets p) bounds)
  let inputs := joined.step (inputFormula (D := D) p)
  obtain ⟨f,hf,ef⟩ := exists_local_cutFrame w inputs
  refine ⟨f,?_,?_⟩
  · have hi := Frame.step_size_le joined (inputFormula (D := D) p) 12 (formula_size p)
    have hcard : Fintype.card Input = 4 := by decide
    simp only [Fintype.card_prod,Fintype.card_fin,hcard,joined,parallelFrame_size,Frame.initial_size,zero_add] at hi
    simp only [Fintype.card_prod,Fintype.card_fin] at hf hb
    change inputs.size ≤ _ at hi
    calc
      _ ≤ inputs.size + 1 + M*Fintype.card (Band D)*(3300*(w+1)^2) := hf
      _ ≤ ((PublicPopulation.offsets p).size + PoolCircuit.scatterCost (Fintype.card A) M D C e k w +
            ((M*Fintype.card (Band D))*(4*w))*12) + 1 + M*Fintype.card (Band D)*(3300*(w+1)^2) :=
        Nat.add_le_add_right (Nat.add_le_add_right (hi.trans (by omega)) _) _
      _ = _ := by ring
  · intro P bits N bin slot x hx fits widths c b r
    let L := Names.denseLayout N slot
    let dense := denseBin N slot bin
    let q := Names.denseSlot N slot c
    let d := liveDescriptor N slot bin perm m (fun a => (code a).val) c b
    have hc : L.width q = N.width c := Names.width_slot N _ _ c
    have hroom := live_fits N slot bin perm m w (fun a => (code a).val) fits c
      ((widths c).symm ▸ value_lt _) b
    apply ef x (slot c,b) d _ hroom.1 hroom.2.1 hroom.2.2 r
    intro field
    cases ha : bin c with
    | none =>
      have inactive : x (p.active (slot c)) = false := (hx.active c).trans (ha ▸ rfl)
      have hfr : d = frozenDescriptor L 0 q b := live_frozen N slot bin perm m _ c ha b
      rw [hfr]
      cases field <;> cases b <;>
        simp [inputs,Frame.step_eval,joined,inputFormula,mux_eval,StatementCircuit.Expr.eval,
          inactive,Input.read,frozenDescriptor,zeroValue]
      all_goals exact (widths c).trans hc.symm
    | some a =>
      have active : x (p.active (slot c)) = true := (hx.active c).trans (ha ▸ rfl)
      have hdense : PublicPopulation.Represents p L dense (denseRows N slot) code x :=
        dense_represents N slot bin p code x hx
      have hd (a : A) : count L dense a < 2^w := (dense_count N slot bin a).trans_lt (fits a)
      have hlabel : dense q = some a := by simpa only [dense,q,denseBin,Function.comp_apply,Equiv.symm_apply_apply] using ha
      have hrow : denseRows N slot q = slot c := by simp [denseRows,q]
      have hget (t : Bool) := eb L dense (denseRows N slot) x hdense hd q a hlabel b t
      rw [hrow] at hget
      have hoff := PublicPopulation.offsets_dense p N bin slot code x hx fits c a ha
      have hfr := live_charged N slot bin perm m (fun a => (code a).val) c a ha b
      change value _ = field.read (liveDescriptor N slot bin perm m _ c b)
      rw [hfr]
      cases field <;>
        simp only [inputs,Frame.step_eval,joined,inputFormula,mux_eval,StatementCircuit.Expr.eval,
          parallelFrame_eval_inl,parallelFrame_eval_inr,Frame.initial_eval,id_eq,active,
          Bool.true_and,ite_true,Input.read,descriptor]
      · exact hoff
      · exact (widths c).trans hc.symm
      · exact hget false
      · exact hget true

end Packing.CutCircuit

end BorderVNP
end Computability
end OAI
