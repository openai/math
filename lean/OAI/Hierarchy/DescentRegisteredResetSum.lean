import OAI.Hierarchy.DescentRegisteredResetSample

namespace OAI
/-! Fixed coefficients for all stages precede both public height parameters.
The finite sum uses one ambient lookup allowance for the executed reset. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters)

def Region (j : Fin 15) (saving : ℕ) : Prop :=
  ∃lead exponent share cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
    G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
    a.Geometry → a.ReachedAt →
    let J:=Nat.log 2 h/(2*B)
    a.charges.paddedAmount a.prefix j ≤ a.hostWork*(lead*scale J exponent)+
      a.groupWork*(lead*scale J exponent)+share*(a.copies/(2^J)^saving)

/-- An invoice inside one physical program may itself be a finite collection of
dated costs. The date-level saving is applied only once after all invoices. -/
theorem of_sum {N : ℕ} (j : Fin 15) (saving : ℕ)
    (cost : ∀{τ B h}, Sample G board op K τ B h → Fin N → ℕ)
    (spent : ∀{τ B h} (a : Sample G board op K τ B h),a.Geometry →
      a.charges.paddedAmount a.prefix j ≤ ∑i,cost a i)
    (parts : ∀i,∃lead exponent share cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
      G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → a.ReachedAt →
      let J:=Nat.log 2 h/(2*B)
      cost a i ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+
        share*(a.copies/(2^J)^saving)) : Region G board op K j saving :=by
  classical
  choose led rate share need estimate using parts
  refine ⟨∑i,led i,∑i,rate i,∑i,share i,∑i,need i,?_⟩
  intro τ B t den large b
  have invoices (i : Fin N):=estimate i τ B t den
    (by have le:=Finset.single_le_sum (s:=Finset.univ) (f:=need) (fun x _=>Nat.zero_le _) (Finset.mem_univ i);omega) b
  filter_upwards [Filter.eventually_all.mpr invoices] with h paid
  intro a g w J
  let U:=scale J (∑i,rate i)
  let high:=a.copies/(2^J)^saving
  have entry (i : Fin N) : cost a i ≤ a.hostWork*(led i*U)+a.groupWork*(led i*U)+share i*high:=by
    have le:=Finset.single_le_sum (s:=Finset.univ) (f:=rate) (fun x _=>Nat.zero_le _) (Finset.mem_univ i)
    have room:scale J (rate i) ≤ U:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
    exact (paid i a g w).trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ room))
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ room))) _)
  apply (spent a g).trans
  have total:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>entry i)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,U,high] using total

theorem join (saving : ℕ) (parts : ∀j,Region G board op K j (saving+1)) :
    ∃lead exponent cutoff : ℕ,∀τ B,0 < τ → 0 < B → 2*τ+cutoff ≤ B →
      G.b ≤ 2^(capRate G K.t K.g) → ∀ᶠ h : ℕ in atTop,∀a : Sample G board op K τ B h,
      a.Geometry → a.ReachedAt →
      let J:=Nat.log 2 h/(2*B)
      a.code.tariff ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+
        a.copies/(2^J)^saving := by
  classical
  unfold Region at parts
  choose coeff rate share minimum region using parts
  refine ⟨∑j,coeff j,∑j,rate j,∑j,minimum j,?_⟩
  intro τ B time den bound branch
  have localBudget (j : Fin 15) :=region j τ B time den
    (by have sub:=Finset.single_le_sum (s:=Finset.univ) (f:=minimum) (fun i _=>Nat.zero_le _) (Finset.mem_univ j);omega) branch
  have every:=Filter.eventually_all.mpr localBudget
  let count:=∑j,share j
  filter_upwards [every,Filter.eventually_ge_atTop (2^(count*(2*B)))] with h estimates late
  intro a geometry reached J
  have room:count ≤ J:=(Nat.le_div_iff_mul_le (by omega : 0 < 2*B)).mpr (Nat.le_log_of_pow_le (by decide) late)
  apply (a.code_paid geometry).trans
  rw [←EnteredCharges.sum_padded]
  exact EnteredCharges.finite_paid _ J _ _ _ saving coeff rate share (fun j=>estimates j a geometry reached)
    (room.trans (Nat.lt_two_pow_self (n:=J)).le)

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
