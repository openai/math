import OAI.Computability.BorderVNP.ShortenPublicRelative

/-!
# Successor rows for inserted terminals and bank sites

The relative seed address and the bank site are a single finite lookup key.
Their canonical chart fixes the lifted position before any counts are known.
The output row applies the shared seed translation to this position and
records the resulting tile together with its next-catalog index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Catalog Epoch Crossing Cover Cover.AddressCircuit BorderVNP.StackFrame RationalHitting
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {I : Type*} [Fintype I] {q D m : ℕ} {K : Type*} [Field K]

/-- Fixed chart position of an inserted public site, indexed by bin and bank site. -/
noncomputable def bankPoint (p : Pattern I D) (e : PaidIdentity K D m) (t : Fin p.bins × BankSite e) :
    HyperbolicHost I := (p.chart t.1).atSite (bankPosition e t.2)

/-- The catalog index of an inserted site is chosen independently of its
seed tile, histogram and private bits. -/
noncomputable def bankIndex (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (t : Fin p.bins × BankSite e) : ↥(p.nextSites e S) :=
  ⟨normalize (bankPoint p e t),
   Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)⟩

/-- The type emitted from the finite key names the exact position in the
posttranslated tile, on its boundary as well as in its interior. -/
theorem bankIndex_exact (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (t : Fin p.bins × BankSite e) (shift : I → gamma 1) :
    (bankIndex p e S t).val = normalize (translatePoint shift (bankPoint p e t)) :=
  (normalize_translate shift (bankPoint p e t)).symm

/-- Semantics of an inserted site descriptor. The input contains just the
one-hot seed/site key and the actual output-level tile of the seed. -/
def BankRow (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d : ℕ) (f : Frame ((Fin p.bins × BankSite e) ⊕ ProductSlots q d)
      (ProductSlots q d ⊕ ↥(p.nextSites e S))) : Prop :=
  ∀ t (shift : I → gamma 1),
    f.eval (Sum.elim (fun v => decide (v=t)) (productWires d fun i => (shift (enum i) : Deck d))) =
      Sum.elim (tileWord enum d (translatePoint shift (bankPoint p e t))) (fun v => decide (v = bankIndex p e S t))

private noncomputable def zeroTileInputs (T : Type*) [Fintype T] (q d : ℕ) :
    Frame (T ⊕ ProductSlots q d) (T ⊕ (ProductSlots q d ⊕ ProductSlots q d)) :=
  (Frame.initial id).step (fun j => match j with
    | .inl t => .input (.inl t)
    | .inr (.inl s) => .input (.inr s)
    | .inr (.inr s) => .const (deckWires d 1 s.2))

private theorem zeroTileInputs_size (T : Type*) [Fintype T] (q d : ℕ) :
    (zeroTileInputs T q d).size ≤ Fintype.card T + 180*q*(d+1) := by
  unfold zeroTileInputs
  apply (Frame.step_size_le _ _ 1 ?_).trans
  · simp [ProductSlots,Slots,width]; ring_nf; exact le_rfl
  · rintro (t | s | s) <;> rfl

set_option maxHeartbeats 1200000 in
/-- One circuit for all seed addresses and profile sites at the indicated depth.
The fixed chart lookup and modular deck multiplication have polynomial cost. -/
theorem bankRow_frames (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∃ f, BankRow enum p e S d f ∧ f.size ≤ C*(d+1)^k := by
  let T := Fin p.bins × BankSite e
  let g (_ : Fin q) : Cover.Frame.SL := 1
  have hg (i) : Cover.Frame.Clears (g i) 0 := Cover.Frame.clears_lattice 1 (Subgroup.one_mem _)
  obtain ⟨M,k,h⟩ := geometricPackRow_frames (T := T) (I := ↥(p.nextSites e S)) hg
  simp only [Nat.mul_zero,Nat.add_zero] at h
  let B : TimeBound := .const (Fintype.card T) + .const (180*q) * TimeBound.variable +
    .const M * TimeBound.variable^k
  obtain ⟨C,u,_,_,hB⟩ := B.growth
  refine ⟨C,u,?_⟩
  intro d hd
  let types (t : T) (i : Fin q) := (bankPoint p e t (enum i)).toSL2R
  let classify (t : T) (_ : Fin q → Cover.Frame.SL) (v : ↥(p.nextSites e S)) := decide (v = bankIndex p e S t)
  obtain ⟨row,hs,he⟩ := h d hd (Equiv.refl _) types classify
  refine ⟨row.subst (zeroTileInputs T q d),?_,?_⟩
  · intro t shift
    let v := Sum.elim (fun s : T => decide (s=t)) (productWires d fun i => (shift (enum i) : Deck d))
    have hread : (zeroTileInputs T q d).eval v = rowInput t (fun i => (shift (enum i) : Deck d)) (fun _ => (1 : Deck d)) := by
      funext j
      rcases j with t | s | s <;> simp [zeroTileInputs,v,rowInput,productWires,Expr.eval]
    change (row.subst _).eval v = _
    funext j
    rw [Frame.subst_eval,hread]
    have hout := he t (fun i => shift (enum i)) (fun _ => (1 : gamma 1))
    simp only [g,Equiv.refl_apply,map_one,one_mul,QuotientGroup.mk_one] at hout
    refine (congrFun hout j).trans ?_
    rcases j with ⟨i,s⟩ | v
    · change deckWires _ (Cover.Frame.frameCarry (gammaSL 1 (shift (enum i)) * types t i) : Deck _) s = _
      rw [Cover.Frame.frameCarry,mul_smul,UpperHalfPlane.toSL2R_smul_I]
      rfl
    · apply Bool.eq_iff_iff.mpr
      simp only [Sum.elim_inr,classify,decide_eq_true_eq]
  · rw [Frame.subst_size]
    have bound := hB (d+1) (by omega)
    simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_variable,
      TimeBound.eval_const] at bound
    exact (Nat.add_le_add (zeroTileInputs_size T q d) hs).trans bound

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
