import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Compaction of the live buy bits of all purchase stages and signs -/

namespace Hierarchy.ProtocolRAMPurchaseFlagPack

open ProtocolRAM ProbeStage.Native Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- Each fixed source bank contains a stage/sign slice with the same row count. -/
def terms {k : ℕ} (source : Fin k → Bank) : List Expr :=
  List.ofFn (fun i => Expr.lookup (source i) .row)

def passes {k : ℕ} (source : Fin k → Bank) (R base : ℕ) := columns R base (terms source)

def code {k : ℕ} (w : ℕ) (source : Fin k → Bank) (R base : ℕ) := program w (passes source R base)

def output {w k : ℕ} (source : Fin k → Bank) (R base : ℕ) (m : Memory w) := result (passes source R base) m

private theorem readers {k w base : ℕ} (source : Fin k → Bank) (fit : ∀ i, (source i).Fits w base) :
    ∀ e∈terms source, e.Fits w base := by
  intro e he
  unfold terms at he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact ⟨fit i,trivial⟩

theorem read {w k : ℕ} (source : Fin k → Bank) (R base : ℕ) (m : Memory w)
    (fit : ∀ i, (source i).Fits w base) (capacity : ∀ i, R≤(source i).size)
    (i : Fin k) (r : Fin R) :
    output source R base m (base+i.val*R+r.val) = m ((source i).base+r.val) := by
  have h := columns_read (terms source) m (src := base) (base := base) le_rfl
    (readers source fit) i.val (by simp [terms]) r
  have lt := r.isLt.trans_le (capacity i)
  simpa only [output,passes,terms,List.getElem_ofFn,Expr.eval,Bank.read,
    Fin.val_cast_of_lt (lt.trans (fit i).2.1),Nat.mod_eq_of_lt lt] using h

theorem execute {w k : ℕ} (source : Fin k → Bank) (R base : ℕ) (m : Memory w)
    (fit : ∀ i, (source i).Fits w base) (room : base+k*R<2^w) :
    (code w source R base).Exec m (output source R base m) (clock (passes source R base)) := by
  exact columns_exec (terms source) m
    (columns_safe (terms source) (src := base) le_rfl (readers source fit) (by simpa [terms] using room))

theorem cheap {k : ℕ} (w : ℕ) (source : Fin k → Bank) (R base : ℕ) :
    CheapCode (code w source R base) := by
  unfold code
  generalize passes source R base = ps
  exact @program_cheap w ps

theorem ticks {k : ℕ} (source : Fin k → Bank) (R base : ℕ) :
    clock (passes source R base) ≤ 4+k*(4+18*R) := by
  have h := columns_clock R base 7 (terms source) (by
    intro e he
    unfold terms at he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    simp [Expr.work])
  simpa [passes,terms,Nat.mul_comm R 18] using h

theorem ticks_of_pos {k : ℕ} (source : Fin k → Bank) (R base : ℕ) (pos : 0<R) :
    clock (passes source R base) ≤ 4+22*(k*R) := by
  have scale : 4+18*R ≤ 22*R := by omega
  have bound := Nat.mul_le_mul_left k scale
  calc
    _ ≤ 4+k*(4+18*R) := ticks source R base
    _ ≤ 4+k*(22*R) := Nat.add_le_add_left bound 4
    _ = _ := by rw [← Nat.mul_assoc,Nat.mul_comm k 22,Nat.mul_assoc]

theorem frame {w k : ℕ} (source : Fin k → Bank) (R base : ℕ) (m : Memory w) (a : ℕ)
    (outside : a<base ∨ base+k*R≤a) : output source R base m a=m a := by
  exact columns_frame (terms source) m (by simpa [terms] using outside)

/-- A single native run packs all dynamically obtained flags, exposing each bit
at its ordinary unpadded joint table index and preserving unrelated words. -/
theorem pack {w k : ℕ} (source : Fin k → Bank) (R base : ℕ) (m : Memory w)
    (fit : ∀ i, (source i).Fits w base) (capacity : ∀ i, R≤(source i).size)
    (room : base+k*R<2^w) :
    let m' := output source R base m
    let t := clock (passes source R base)
    (code w source R base).Exec m m' t ∧ CheapCode (code w source R base) ∧ t ≤ 4+k*(4+18*R) ∧
      (∀ (i : Fin k) (r : Fin R), m' (base+i.val*R+r.val)=m ((source i).base+r.val)) ∧
      ∀ a, (a<base ∨ base+k*R≤a) → m' a=m a := by
  exact ⟨execute source R base m fit room,cheap w source R base,ticks source R base,
    read source R base m fit capacity,frame source R base m⟩


end Hierarchy.ProtocolRAMPurchaseFlagPack

end OAI
