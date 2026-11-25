import OAI.Computability.BorderVNP.ShortenPublicRelativeRounds
import OAI.Computability.BorderVNP.ShortenPublicRelativeBank
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-!
# Parallel site reconstruction on stable public row numbers

All retained sites of a copy read the very same selected motion and deck
translation. All inserted sites of a seed read the same bin and output tile.
A bank-site tag is hardwired by its row in the seed's fixed bank rectangle.
The batch uses one depth-polynomial gate allowance for each reserved site.
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

/-- Shared per-copy fields, retained per-site fields and shared per-seed fields. -/
abbrev BatchPorts (q : ℕ) (p : Pattern I D) (S : Finset (HyperbolicHost I)) (d copies sites seeds : ℕ) :=
  (Fin copies × (Fin p.moves ⊕ ProductSlots q (d+2*p.depth))) ⊕
  (Fin sites × (↥S ⊕ ProductSlots q (d+2*p.depth+2*p.depth))) ⊕
  (Fin seeds × (Fin p.bins ⊕ ProductSlots q (d+2*p.depth)))

/-- Numbering used by the packed site rows, including padding and all fixed bank sites. -/
noncomputable def siteOrdinal (e : PaidIdentity K D m) (sites seeds : ℕ) :
    Fin sites ⊕ (Fin seeds × BankSite e) ≃ Fin (StaticRows.siteCapacity e sites seeds) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _)
    (Fintype.equivFin (BankSite e))).trans finProdFinEquiv)).trans finSumFinEquiv

/-- Wiring of one old site. Its selected candidate and shift are shared with
all other sites whose stable numbers belong to the same copy. -/
def oldPin (q : ℕ) (p : Pattern I D) (S : Finset (HyperbolicHost I)) (d : ℕ)
    {copies sites seeds : ℕ} (home : Fin sites → Fin copies) (r : Fin sites) :
    Fin p.moves ⊕ (↥S ⊕ (ProductSlots q (d+2*p.depth) ⊕ ProductSlots q (d+2*p.depth+2*p.depth))) →
      BatchPorts q p S d copies sites seeds
  | .inl n => .inl (home r,.inl n)
  | .inr (.inl t) => .inr (.inl (r,.inl t))
  | .inr (.inr (.inl s)) => .inl (home r,.inr s)
  | .inr (.inr (.inr s)) => .inr (.inl (r,.inr s))

/-- Read the seed bin and tile and form the joint bin/site tag of this bank row. -/
noncomputable def bankRead (q : ℕ) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d copies sites : ℕ) {seeds : ℕ} (a : Fin seeds) (v : BankSite e) :
    Frame (BatchPorts q p S d copies sites seeds) ((Fin p.bins × BankSite e) ⊕ ProductSlots q (d+2*p.depth)) :=
  (Frame.initial id).step fun j => match j with
    | .inl (k,u) => if u=v then .input (.inr (.inr (a,.inl k))) else .const false
    | .inr s => .input (.inr (.inr (a,.inr s)))

private theorem bankRead_size (q : ℕ) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d copies sites : ℕ) {seeds : ℕ} (a : Fin seeds) (v : BankSite e) :
    (bankRead q p e S d copies sites a v).size ≤ p.bins*Fintype.card (BankSite e) + 90*q*(d+2*p.depth+1) := by
  unfold bankRead
  apply (Frame.step_size_le _ _ 1 ?_).trans_eq
  · simp [ProductSlots,Slots,width]; ring
  · rintro (⟨k,u⟩ | s)
    · by_cases h : u=v <;> simp [h,Expr.size]
    · rfl

/-- Correctness of the hardwired bank-site tag requires only the seed bin and its tile. -/
theorem bankRead_eval (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d copies sites : ℕ) {seeds : ℕ} (a : Fin seeds)
    (v : BankSite e) (z : BatchPorts q p S d copies sites seeds → Bool)
    (k : Fin p.bins) (shift : I → gamma 1)
    (hz : ∀ s, z (.inr (.inr (a,s))) = Sum.elim (fun u => decide (u=k))
      (productWires _ fun i => (shift (enum i) : Deck _)) s) :
    (bankRead q p e S d copies sites a v).eval z =
      Sum.elim (fun u => decide (u=(k,v))) (productWires _ fun i => (shift (enum i) : Deck _)) := by
  funext j
  rcases j with ⟨h,u⟩ | s
  · by_cases he : u=v
    · subst u
      simp [bankRead,Expr.eval,hz]
    · simp [bankRead,he,Expr.eval]
  · simp [bankRead,Expr.eval,hz]

/-- Physical output of any occupied site row. Each premise describes just the
fields read by this row, so arbitrary padding rows never require catalog data. -/
structure BatchRows (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d : ℕ) {copies sites seeds : ℕ} (home : Fin sites → Fin copies)
    (f : Frame (BatchPorts q p S d copies sites seeds) (Fin (StaticRows.siteCapacity e sites seeds) ×
      (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)))) : Prop where
  /-- Semantics at an occupied retained row. -/
  old : ∀ (z : BatchPorts q p S d copies sites seeds → Bool) r n shift x (hx : normalize x ∈ S),
    z ∘ oldPin q p S d home r = Sum.elim (fun u => decide (u=n)) (siteInput enum S _ _ shift x hx) →
      ∀ j, f.eval z (siteOrdinal e sites seeds (.inl r),j) =
        Sum.elim (tileWord enum _ (moved p n shift x)) (fun t => decide (t = movedIndex p e S n shift x hx)) j
  /-- Semantics at an occupied seed rectangle. -/
  bank : ∀ (z : BatchPorts q p S d copies sites seeds → Bool) a v k (shift : I → gamma 1),
    (∀ s, z (.inr (.inr (a,s))) = Sum.elim (fun u => decide (u=k))
      (productWires _ fun i => (shift (enum i) : Deck _)) s) →
      ∀ j, f.eval z (siteOrdinal e sites seeds (.inr (a,v)),j) =
        Sum.elim (tileWord enum _ (translatePoint shift (bankPoint p e (k,v))))
          (fun t => decide (t = bankIndex p e S (k,v))) j

set_option maxHeartbeats 1200000 in
/-- The gate bound is linear in the number of reserved sites times a fixed
polynomial in the cover depth. There is no multiplicative bit-width or tile-count scan. -/
theorem batchRow_frames (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ (copies sites seeds : ℕ) (home : Fin sites → Fin copies),
      ∃ f, BatchRows enum p e S d (seeds := seeds) home f ∧
        f.size ≤ (1 + StaticRows.siteCapacity e sites seeds) * C * (d+1)^k := by
  obtain ⟨M,u,hM⟩ := motionRow_frames enum p e S
  obtain ⟨B,v,hB⟩ := bankRow_frames enum p e S
  let l : TimeBound := TimeBound.variable + .const (2*p.depth)
  let bound : TimeBound := 1 + .const M * TimeBound.variable^u + .const (p.bins*Fintype.card (BankSite e)) +
    .const (90*q)*l + .const B*l^v
  obtain ⟨C,k,hC,_,hc⟩ := bound.growth
  refine ⟨C,k,?_⟩
  intro d hd copies sites seeds home
  let o := d+2*p.depth
  obtain ⟨old,hold,hs⟩ := hM d hd
  obtain ⟨bank,hbank,ht⟩ := hB o (by dsimp [o]; omega)
  let Row := Fin sites ⊕ (Fin seeds × BankSite e)
  let Y := ProductSlots q o ⊕ ↥(p.nextSites e S)
  let lane : Row → Frame (BatchPorts q p S d copies sites seeds) Y := Sum.elim
    (fun r => old.subst (Frame.initial (oldPin q p S d home r)))
    (fun a => bank.subst (bankRead q p e S d copies sites a.1 a.2))
  obtain ⟨out,hout,he⟩ := exists_parallelFrames (out := fun _ : Row => Y) lane
  refine ⟨out.select (fun j => ⟨(siteOrdinal e sites seeds).symm j.1,j.2⟩),⟨?_,?_⟩,?_⟩
  · intro z r n shift x hx hz j
    rw [Frame.select_eval,Equiv.symm_apply_apply,he]
    change (old.subst (Frame.initial (oldPin q p S d home r))).eval z j = _
    have read : (Frame.initial (oldPin q p S d home r)).eval z = z ∘ oldPin q p S d home r :=
      funext (Frame.initial_eval _ _)
    rw [Frame.subst_eval,read,hz]
    exact congrFun (hold n shift x hx) j
  · intro z a v k shift hz j
    rw [Frame.select_eval,Equiv.symm_apply_apply,he]
    change (bank.subst (bankRead q p e S d copies sites a v)).eval z j = _
    rw [Frame.subst_eval,bankRead_eval enum p e S d copies sites a v z k shift hz]
    exact congrFun (hbank (k,v) shift) j
  · have hl : l.eval (d+1) = o+1 := by simp [l,o]; omega
    have hb := hc (d+1) (by omega)
    simp only [bound,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_numeral,
      TimeBound.eval_const,TimeBound.eval_variable,hl] at hb
    have hlane (r : Row) : (lane r).size ≤ C*(d+1)^k := by
      rcases r with r | ⟨a,v⟩
      · change (old.subst (Frame.initial _)).size ≤ _
        rw [Frame.subst_size,Frame.initial_size,zero_add]
        omega
      · change (bank.subst (bankRead q p e S d copies sites a v)).size ≤ _
        rw [Frame.subst_size]
        have h := bankRead_size q p e S d copies sites a v
        change _ ≤ p.bins*Fintype.card (BankSite e) + 90*q*(o+1) at h
        omega
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlane i)
    have hcard : Fintype.card Row = StaticRows.siteCapacity e sites seeds :=
      (Fintype.card_congr (siteOrdinal e sites seeds)).trans (Fintype.card_fin _)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard] at hsum
    have hone : 1 ≤ C*(d+1)^k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hC.ne' (pow_ne_zero _ (by omega)))
    rw [Frame.select_size,add_mul,one_mul,Nat.add_mul,Nat.mul_assoc]
    exact hout.trans (Nat.add_le_add hone hsum)

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
