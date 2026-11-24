import OAI.Computability.VPVNP.CompressorBundleKeyTable
import OAI.Computability.VPVNP.CompressorRecordsShrinkRAM

/-!
# A fixed-bank worker for gathering the complete pair of bundle key tables

The cursor visits a packed port's thick-wire entries followed by its motif
entries. The physical rectangular arrays keep all thick rows first and all
motif rows second. Integer division and a single bit computed from the
within-port position give the correct physical row without changing the
public parameter bank between calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather.Fixed

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open ShrinkRAM (div mod)

variable {w : ℕ}

/-- Encode a natural table size, index or address as a machine word of the chosen width. -/
abbrev word (j : ℕ) : Word w := Fin.ofNat (2^w) j

/-- Public words are the total per port, thick entries per port, port count,
row stride, ID base, classifier key base, and gathered key base. -/
def visit : List (Op 8 7) :=
  [.stateWord 0, .publicWord 1 0, .binary .div 2 0 1, .binary .mod 3 0 1,
   .publicWord 4 1, .constant 5 1, .binary .add 6 3 5, .binary .div 6 4 6,
   .binary .div 6 6 6, .binary .sub 6 5 6, .publicWord 7 2, .binary .mul 7 6 7,
   .binary .add 2 2 7, .publicWord 7 3, .binary .mul 2 2 7, .binary .mul 7 6 4,
   .binary .sub 3 3 7, .binary .add 2 2 3, .publicWord 7 4, .binary .add 7 7 2,
   .read 1 7, .publicWord 7 5, .binary .add 7 7 1, .read 1 7,
   .publicWord 7 6, .binary .add 7 7 2, .write 7 1, .binary .add 0 0 5]

/-- The quotient test is positive exactly in the thick part of a port. -/
def offset (p : Fin 7 → Word w) (i : Word w) : Word w :=
  let z := mod i (p 0)
  let ratio := div (p 1) (z+1)
  let cd := 1 - div ratio ratio
  (div i (p 0) + cd * p 2) * p 3 + (z - cd * p 1)

/-- The visit reads the stored arc identifier, looks up its key, and writes that key into the
corresponding output slot. -/
def events (p : Fin 7 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let off := offset p i
  let src := p 4+off
  let id := m src.val
  let keyAddr := p 5+id
  let key := m keyAddr.val
  List.replicate 20 .tick ++ [.read src id,.tick,.tick,.read keyAddr key,.tick,.tick,.write (p 6+off) key,.tick]

theorem native (p : Fin 7 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 29 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  change execute ((template visit 0).instantiate w p).program (1+visit.length) ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  rfl

theorem after_events (p : Fin 7 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) =
      writeMemory m (p 6+offset p i) (m (p 5 + m (p 4+offset p i).val).val) := rfl

theorem work (p : Fin 7 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 28 ∧ countProbes (events p m i) = 3 := ⟨rfl,rfl⟩

end CompressorRecords.BundleGather.Fixed

end VPVNP
end Computability
end OAI
