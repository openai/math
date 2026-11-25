import OAI.ThreeFlat.Diagonal.LaneCursorCanonical
import OAI.ThreeFlat.RAM.EffectLocation

namespace OAI
/-! # A linear-time sparse inverse for the public XOR-mask list -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout
open Computability.VPVNP.BurstRAM PrivateRAM RAM.EffectStream RAM
open scoped Fin.CommRing
variable {F : Type*} {p k low o c W : ℕ} {N : BitNetwork F p} (P : RowLayout N k low o c)

/-- Two words per public mask are sufficient even when the masks span the
entire exponential address range. Aliases write the same canonical index. -/
def dictionary (base : ℕ) : List (Record W) :=
  List.ofFn (fun j => ((base+(P.offset j).val : ℕ),(firstIndex P.offset j).val))

@[simp] theorem dictionary_length (base : ℕ) : (P.dictionary (W:=W) base).length=o :=
  List.length_ofFn

theorem read_dictionary (base : ℕ) (m : Memory W) (fit : base+2^k*2^low ≤ 2^W) (i : Fin o) :
    after m (events (P.dictionary base)) (base+(P.offset i).val) =
      ((firstIndex P.offset i).val : Word W) := by
  apply after_at
  · intro rec mem hit
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
    have hj : base+(P.offset j).val<2^W := by have := (P.offset j).isLt; omega
    change ((base+(P.offset j).val : ℕ) : Word W).val=_ at hit
    rw [Fin.val_cast_of_lt hj] at hit
    have same : P.offset j=P.offset i := Fin.ext (by omega)
    exact congrArg (fun z : Fin o => (z.val : Word W)) (firstIndex_congr _ same)
  · right
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    apply Fin.val_cast_of_lt
    have := (P.offset i).isLt
    omega

theorem dictionary_safe (base src : ℕ) (fit : base+2^k*2^low ≤ 2^W)
    (apart : src+2*o ≤ base ∨ base+2^k*2^low ≤ src) :
    Safe src (P.dictionary (W:=W) base) := by
  intro rec mem
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
  have hi := (P.offset j).isLt
  have ha : base+(P.offset j).val<2^W := by omega
  change ((base+(P.offset j).val : ℕ) : Word W).val<src ∨
    src+2*(P.dictionary (W:=W) base).length≤((base+(P.offset j).val : ℕ) : Word W).val
  rw [Fin.val_cast_of_lt ha,dictionary_length]
  omega

/-- One six-label deterministic native block writes the entire sparse
inverse list, in 1+6o instructions. Untouched addresses in its ambient
region have no effect on the row lookups. -/
theorem mass_dictionary {G : Type*} [Semiring G] {pcCount regCount litCount : ℕ}
    (field : FieldCode G W) (M : Machine W pcCount regCount litCount)
    (pc : Fin 6 → Fin pcCount) (regs : Fin 5 ↪ Fin regCount) (exit : Fin pcCount)
    (compiled : ∀ j, M.code (pc j)=block pc regs exit j)
    (base src fuel : ℕ) (cfg : Config W pcCount regCount) (m : Memory W)
    (fit : base+2^k*2^low ≤ 2^W) (apart : src+2*o ≤ base ∨ base+2^k*2^low ≤ src)
    (entry : cfg.pc=pc 0) (start : (cfg.reg (regs 0)).val=src)
    (doneAt : (cfg.reg (regs 1)).val=src+2*o) (one : cfg.reg (regs 4)=1)
    (loaded : Loaded m src (P.dictionary base)) :
    mass field M.program (fuel+1+6*o) cfg m =
      mass field M.program fuel (endConfig regs pc exit (P.dictionary base) cfg)
        (after m (events (P.dictionary base))) := by
  simpa only [dictionary_length] using mass_block field M pc regs exit compiled src
    (P.dictionary base) fuel cfg m entry start (by simpa only [dictionary_length] using doneAt)
    one loaded (P.dictionary_safe base src fit apart)

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
