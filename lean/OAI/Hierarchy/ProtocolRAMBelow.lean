import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Agreement below a public address cutoff for native finite scans -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w cut : ℕ} {m n : Memory w}

def Below (cut : ℕ) (m n : Memory w) : Prop := ∀x,x<cut→m x=n x

namespace Below

theorem mono {smaller : ℕ} (h : Below cut m n) (le : smaller≤cut) : Below smaller m n :=
  fun x hx=>h x (hx.trans_le le)

theorem expr (h : Below cut m n) (e : Expr) (r : Word w) {out : ℕ}
    (fit : e.Fits w out) (threshold : out≤cut) : e.eval m r=e.eval n r :=
  eval_below e r n m fit (h.mono threshold)

theorem bank (h : Below cut m n) (b : Bank) (r : Word w) (high : b.base+b.size≤cut) :
    b.read m r=b.read n r :=
  h _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le high)

theorem fill (h : Below cut m n) (base count : ℕ) (f g : ℕ→Word w)
    (row : ∀x,base≤x→x<base+count→x<cut→f x=g x) :
    Below cut (fillSegment base count f m) (fillSegment base count g n) := by
  intro x hx
  unfold fillSegment
  split
  next hit => exact row x hit.1 hit.2 hx
  next => exact h x hx

theorem scan (h : Below cut m n) (out rows : ℕ) (e : Expr) (fits : e.Fits w out)
    (hi : out≤cut) : Below cut (image out rows e m) (image out rows e n) :=
  h.fill _ _ _ _ fun _ _ _ _=>h.expr _ _ fits hi

theorem pass (h : Below cut m n) (p : Pass) (fits : p.Fits w) (hi : p.out≤cut) :
    Below cut (p.apply m) (p.apply n) := h.scan _ _ _ fits.1 hi

theorem passes (h : Below cut m n) (ps : List Pass) (ready : ∀p∈ps,p.Fits w ∧ p.out≤cut) :
    Below cut (result ps m) (result ps n) := by
  induction ps generalizing m n with
  | nil => exact h
  | cons p ps ih =>
    obtain ⟨fit,hi⟩ := ready p (List.mem_cons_self ..)
    exact ih (h.pass p fit hi) (fun q hq=>ready q (List.mem_cons_of_mem _ hq))

end Below

end Hierarchy.ProtocolRAM.Calendar

end OAI
