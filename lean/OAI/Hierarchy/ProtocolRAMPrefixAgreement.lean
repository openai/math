import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Causality below the largest readable address of native scan passes -/

namespace Hierarchy.ProtocolRAM.PrefixAgreement
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
variable {w : ℕ}

def Low (cut : ℕ) (left right : Memory w) := ∀x< cut,left x=right x

theorem expr (e : Expr) (left right : Memory w) (cut : ℕ) (h : e.inputEnd≤ cut)
    (σ : Low cut left right) (r : Word w) : e.eval left r=e.eval right r := by
  induction e with
  | row | lit => rfl
  | lookup b i ih =>
    obtain ⟨bank,dep⟩:=max_le_iff.mp h
    simp only [Expr.eval,ih dep,Bank.read]
    apply σ
    have reduced:=Nat.mod_lt (i.eval right r).val (Nat.two_pow_pos b.bits)
    change (i.eval right r).val%b.size< b.size at reduced
    omega
  | op o u v lu lv =>
    obtain ⟨a,b⟩:=max_le_iff.mp h
    simp only [Expr.eval,lu a,lv b]
  | branch t u v a b lu lv la lb =>
    obtain ⟨huv,hab⟩:=max_le_iff.mp h
    obtain ⟨hu,hv⟩:=max_le_iff.mp huv
    obtain ⟨ha,hb⟩:=max_le_iff.mp hab
    simp only [Expr.eval,lu hu,lv hv,la ha,lb hb]

theorem inputEnd_of_fits (e : Expr) {w bound : ℕ} (h : e.Fits w bound) : e.inputEnd≤ bound := by
  induction e with
  | row | lit => exact Nat.zero_le _
  | lookup b i ih => exact max_le h.1.2.2 (ih h.2)
  | op _ _ _ lu lv => exact max_le (lu h.1) (lv h.2)
  | branch _ _ _ _ _ lu lv la lb => exact max_le (max_le (lu h.1) (lv h.2.1)) (max_le (la h.2.2.1) (lb h.2.2.2))

theorem pass (p : Pass) (left right : Memory w) (cut : ℕ) (h : p.term.inputEnd≤ cut)
    (σ : Low cut left right) : Low cut (p.apply left) (p.apply right) := by
  intro x hx
  change (if p.out≤ x ∧ x< p.out+p.rows then _ else left x)=
    (if p.out≤ x ∧ x< p.out+p.rows then _ else right x)
  split
  · exact expr _ _ _ _ h σ _
  · exact σ x hx

theorem passes (ps : List Pass) (left right : Memory w) (cut : ℕ) (h : ∀p∈ps,p.term.inputEnd≤ cut)
    (σ : Low cut left right) : Low cut (result ps left) (result ps right) := by
  induction ps generalizing left right with
  | nil => exact σ
  | cons p ps ih =>
    have head:=h p (List.mem_cons_self ..)
    exact ih _ _ (fun u hu=> h u (List.mem_cons_of_mem _ hu)) (pass p _ _ cut head σ)

end Hierarchy.ProtocolRAM.PrefixAgreement

end OAI
