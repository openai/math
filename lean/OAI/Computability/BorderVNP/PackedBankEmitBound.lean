import OAI.Computability.BorderVNP.PackedBankEmit
import OAI.Computability.BorderVNP.PackedBankHeaderCapacity

/-! # Word-width sufficiency for the complete packet emitter

A fixed static coefficient bounds every intermediate address expression, including
relocation of canonical ports. The physical local-record cap controls the count
headers even for a zero-width selector. Together with the actual cell address
bound this removes individual word-fit premises from the packet theorem.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open Word Crossing Shortening Shortening.StaticRows Shortening.CombiningStep Shortening.SeedIntervals
open ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

private def coefficient {I : Type*} : WidthExpr I → ℕ
  | .const n => n + 1
  | .field _ => 1
  | .binary _ a b => coefficient a + coefficient b

private theorem op_bound (op : Op) (a b : ℕ) : op.apply a b ≤ a+b := by
  cases op <;> simp [Op.apply]
  omega

private theorem eval_bound {I : Type*} (e : WidthExpr I) (x : I → ℕ) (B : ℕ) (h : ∀ i, x i ≤ B) :
    e.eval x ≤ coefficient e * (B+1) := by
  induction e with
  | field i => simpa only [WidthExpr.eval,coefficient,one_mul] using (h i).trans (Nat.le_succ B)
  | const n =>
    exact (Nat.le_succ n).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos B))
  | binary op a b ia ib =>
    exact (op_bound _ _ _).trans ((Nat.add_le_add ia ib).trans_eq (Nat.add_mul _ _ _).symm)

private theorem fits_bound {I : Type*} (e : WidthExpr I) (x : I → ℕ) (B w : ℕ) (h : ∀ i, x i ≤ B)
    (room : coefficient e * (B+1) < 2^w) : e.Fits w x := by
  induction e with
  | field i => exact (eval_bound (.field i) x B h).trans_lt room
  | const n => exact (eval_bound (.const n) x B h).trans_lt room
  | binary op a b ia ib =>
    change (coefficient a + coefficient b)*(B+1) < 2^w at room
    rw [Nat.add_mul] at room
    exact ⟨ia (by omega),ib (by omega),(eval_bound (.binary op a b) x B h).trans_lt
      (by simpa only [coefficient,Nat.add_mul] using room)⟩

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- Static coefficient sufficient for all intermediate addresses of every seed site. -/
noncomputable def addressCoefficient : ℕ := 1 + ∑ z : Output e first, coefficient (expr e first z)

/-- Simultaneous output width sufficiency from one bound on the prepared public values. -/
theorem fits_all {w B : ℕ} (raw : Raw e → ℕ) (h : ∀ r, word e raw r ≤ B)
    (room : addressCoefficient e first * (B+1) < 2^w) (z : Output e first) :
    (expr e first z).Fits w (fun i => word e raw (pin e z.1 i)) := by
  have hz : coefficient (expr e first z) ≤ addressCoefficient e first :=
    (Finset.single_le_sum (f := fun t => coefficient (expr e first t)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ z)).trans (Nat.le_add_left _ _)
  exact fits_bound _ _ B w (fun _ => h _) ((Nat.mul_le_mul_right _ hz).trans_lt room)

/-- A genuine physical branch supplies all the arithmetic fit obligations, with
location fields bounded by the cell's actual finite bank and directory sizes. -/
theorem fits_physical [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (q : Counts e p bin perm) {T : Type*} (hm : 0 < m)
    (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : ∀ t, localRecords (output e p bin perm positive first q).layout true
      (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
      (fun v => tile v = t) ≤ M)
    (s : S) {w addressMax : ℕ} (raw : Raw e → ℕ)
    (counts : ∀ i, raw (.inl i) = i.elim (blocks p.layout bin perm m s) (q s).val)
    (loc : ∀ z, raw (.inr z) ≤ addressMax)
    (room : addressCoefficient e first * (max (BankCharges.bound e * M) addressMax + 1) < 2^w) :
    Fits e w raw ∧ ∀ z : Output e first, (expr e first z).Fits w (fun i => word e raw (pin e z.1 i)) := by
  let j := blocks p.layout bin perm m s
  let p' := (q s).val
  let B := max (BankCharges.bound e * M) addressMax
  have hcounts : (fun i => raw (.inl i)) = (fun i => i.elim j p') := funext counts
  obtain ⟨hh,hb⟩ := BankCharges.header_le_of_tile_cap e p bin perm positive first q hm tile prior payload M cap s
  have hhead : ∀ r, word e raw r ≤ B := by
    intro r
    rcases r with h | ⟨a,v,h⟩ | z
    · change BankCircuit.headerWord m (fun i => raw (.inl i)) h ≤ B
      rw [hcounts]
      exact (hh h).trans (le_max_left _ _)
    · change PaidBox.header (PaidBox.widths (e.net a) v) (raw (.inl (some a))) h ≤ B
      rw [counts]; exact (hb a v h).trans (le_max_left _ _)
    · exact (loc z).trans (le_max_right _ _)
  have hpos : 0 < addressCoefficient e first := by unfold addressCoefficient; omega
  have hsmall : B < 2^w := (Nat.le_succ B).trans_lt ((Nat.le_mul_of_pos_left _ hpos).trans_lt room)
  refine ⟨⟨?_, fun u => (hhead (.inr (.inl u))).trans_lt hsmall⟩,fits_all e first raw hhead room⟩
  rw [hcounts]
  have site (v : TemplateSite e) : BankCharges.volume e j p' v ≤ B :=
    (Nat.le_add_left _ _).trans ((BankCharges.site_le e p bin perm positive first q tile prior payload M cap s v).trans
      (le_max_left _ _))
  exact BankCircuit.headerFits_of_capacity m w j p' (profileCounts_total e _ q s)
    ((site (.inl ())).trans_lt hsmall) ((site (.inr (.inl first))).trans_lt hsmall)

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
