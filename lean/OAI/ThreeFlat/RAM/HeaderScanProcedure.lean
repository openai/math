import OAI.ThreeFlat.RAM.HeaderScan
import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.PhysicalPinsExpr

namespace OAI
/-! # Memory-only stage-header scans and sequential composition -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalPinsExpr PhysicalProcedure

open scoped Fin.CommRing
variable {w n : ℕ}

/-- Compile a memory-only descriptor. Optional public parameters are grounded
at zero; the stage-specific descriptors use only literals, the current address
and external-memory reads. -/
def closed : Formula n → Term w 0 n
  | .reg i => .result i
  | .lit a => .literal (a : Word w)
  | .param _ => .literal 0
  | .op b x y => .binary b (closed x) (closed y)
  | .cut x y => .select .lt (closed x) (closed y) (.literal 0) (.binary .sub (closed x) (closed y))
  | .load x => .load (closed x)
  | .select q x y a b => .select q (closed x) (closed y) (closed a) (closed b)

theorem eval_closed (f : Formula n) (pub : Fin 0 → Word w) (mem : Memory w) (vs : Fin n → Word w) :
    (closed f).eval pub mem vs = f.value (fun _ => 0) mem vs := by
  induction f <;> simp [closed,Formula.value,Term.eval, *]

theorem binds_closed (f : Formula n) : (closed f : Term w 0 n).binds = f.work := by
  induction f <;> simp [closed,Formula.work,Term.literal,Term.binary,Term.select,Term.load,Term.binds, *] <;> omega

def procedure (current : Word w) (start length : ℕ) (e : Term w 0 1) : Procedure w :=
  ⟨13+e.labels,4+e.binds,0,block e current start length,Fin.elim0⟩

/-- Per-pass functional correctness only requires its row descriptor to be
stable while already-processed output positions are overwritten. -/
theorem spec (current : Word w) (start length : ℕ) (e : Term w 0 1)
    (pre : Memory w → Prop) (lo num : Memory w → ℕ) (words : Memory w → ℕ → Word w) (budget : ℕ)
    (bounds : ∀ m, pre m → lo m+num m < 2^w ∧ 13+num m*(2*e.binds+4)≤budget)
    (header : ∀ m, pre m → m (m current.val+(start:Word w)).val = (lo m : Word w) ∧
      m (m current.val+(length:Word w)).val = (num m : Word w))
    (correct : ∀ m, pre m → ∀ (a : Word w) (m' : Memory w), lo m ≤ a.val → a.val < lo m+num m →
      agreesOutside (lo m) (lo m+num m) m' m → e.eval Fin.elim0 m' (fun _ => a) = words m a.val) :
    (procedure current start length e).Spec pre (fun m o => o=fillSegment (lo m) (num m) (words m) m) budget := by
  intro P R K M pc reg pub exit installed _ c m hp hm
  obtain ⟨t,ht,out,hout,run⟩ := advance_block e current start length (lo m) (num m)
    (bounds m hm).1 pc reg pub exit M installed c m hp (words m) (header m hm).1 (header m hm).2
    (fun a m' h₁ h₂ agree => by
      have empty : (M.publicData ∘ pub : Fin 0 → Word w) = Fin.elim0 := funext fun i => i.elim0
      exact (congrArg (fun p : Fin 0 → Word w => e.eval p m' (fun _ => a)) empty).trans
        (correct m hm a m' h₁ h₂ agree))
  exact ⟨t,ht.trans (bounds m hm).2,out,_,run,hout,rfl⟩

end ThreeFlat.RAM.HeaderScan

end OAI
