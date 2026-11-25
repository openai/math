import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.ExpressionArgumentReads

namespace OAI
/-! # Bounding the physical reads of an eagerly evaluated stage formula -/

namespace ThreeFlat.RAM.HistoryStageBounds
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

variable {n W : ℕ}

abbrev value (W : ℕ) (m : ℕ→ℕ) (vs : Fin n→ℕ) (f : Formula n) : ℕ :=
  f.natural W (fun _ => 0) m vs

abbrev Cell (W : ℕ) (ok : ℕ→Prop) (address : ℕ) : Prop := address<2^W ∧ ok address

/-- All address terms and both operands of the compiled conditional are
evaluated before its output word is selected. -/
def Checked (W : ℕ) (ok : ℕ→Prop) (m : ℕ→ℕ) (vs : Fin n→ℕ) : Formula n→Prop
  | .reg _ | .lit _ | .param _ => True
  | .op o x y => Checked W ok m vs x ∧ Checked W ok m vs y ∧ opFits W o (value W m vs x) (value W m vs y)
  | .cut x y => Checked W ok m vs x ∧ Checked W ok m vs y ∧ value W m vs x<2^W ∧ value W m vs y<2^W
  | .load x => Checked W ok m vs x ∧ Cell W ok (value W m vs x)
  | .select _ x y a b => Checked W ok m vs x ∧ Checked W ok m vs y ∧ value W m vs x<2^W ∧
      value W m vs y<2^W ∧ Checked W ok m vs a ∧ Checked W ok m vs b

theorem Checked.fits {ok : ℕ→Prop} {m : ℕ→ℕ} {vs : Fin n→ℕ} {f : Formula n}
    (h : Checked W ok m vs f) : f.Fits W (fun _ => 0) m vs := by
  induction f with
  | reg | lit | param => trivial
  | op o x y ix iy => exact ⟨ix h.1,iy h.2.1,h.2.2⟩
  | cut x y ix iy => exact ⟨ix h.1,iy h.2.1,h.2.2⟩
  | load x ix => exact ⟨ix h.1,h.2.1⟩
  | select q x y a b ix iy ia ib =>
    obtain ⟨hx,hy,lx,ly,ha,hb⟩ := h
    refine ⟨ix hx,iy hy,lx,ly,?_⟩
    split <;> first | exact ia ha | exact ib hb

theorem Checked.closed_eval {ok : ℕ→Prop} {mem : Memory W} {vs : Fin n→ℕ} {f : Formula n}
    (h : Checked W ok (fun a => (mem a).val) vs f) :
    (HeaderScan.closed f).eval Fin.elim0 mem (fun i => (vs i : Word W)) =
      (value W (fun a => (mem a).val) vs f : Word W) := by
  rw [HeaderScan.eval_closed]
  have words : (fun a => ((mem a).val : Word W)) = mem := funext fun a => Fin.cast_val_eq_self (mem a)
  simpa only [value,Nat.cast_zero,words] using
    f.value_eq_natural (fun _ => 0) (fun a => (mem a).val) vs h.fits

/-- Every physical load in the chronological execution has an allowed
address. This includes the arbitrary values produced by unused arms. -/
theorem Checked.reads {ok : ℕ→Prop} {mem : Memory W} {vs : Fin n→ℕ} {f : Formula n}
    (h : Checked W ok (fun a => (mem a).val) vs f) :
    ∀ p∈(HeaderScan.closed f).reads Fin.elim0 mem (fun i => (vs i : Word W)), ok p := by
  induction f with
  | reg i => simp [HeaderScan.closed,Term.reads]
  | lit v => simp [HeaderScan.closed]
  | param i => simp [HeaderScan.closed]
  | op o x y ix iy =>
    intro p hp
    simp only [HeaderScan.closed,Term.reads_binary,List.mem_append] at hp
    exact hp.elim (ix h.1 p) (iy h.2.1 p)
  | cut x y ix iy =>
    intro p hp
    simp only [HeaderScan.closed,Term.reads_select,Term.reads_binary,Term.reads_literal,List.mem_append,
      List.not_mem_nil,false_or] at hp
    have left := ix h.1 p
    have right := iy h.2.1 p
    tauto
  | load x ix =>
    intro p hp
    obtain ⟨hx,fit,allow⟩ := h
    simp only [HeaderScan.closed,Term.reads_load,List.mem_append,List.mem_singleton] at hp
    rcases hp with prior|last
    · exact ix hx p prior
    · rw [hx.closed_eval,Fin.val_cast_of_lt fit] at last
      exact last.symm ▸ allow
  | select q x y a b ix iy ia ib =>
    obtain ⟨hx,hy,lx,ly,ha,hb⟩ := h
    intro p hp
    simp only [HeaderScan.closed,Term.reads_select,List.mem_append] at hp
    exact hp.elim (ix hx p) (fun more => more.elim (iy hy p)
      (fun arms => arms.elim (ia ha p) (ib hb p)))

end ThreeFlat.RAM.HistoryStageBounds

end OAI
