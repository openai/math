import OAI.ThreeFlat.RAM.TraceBucketSkeleton
import OAI.ThreeFlat.RAM.TraceBucketAtomSize

namespace OAI
/-! # One fixed initial-atom ROM for every physically addressed trace -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open DescriptorExpr.LiteralBank

def bankSize := 1000001

private def blank : Layout :=
  ⟨⟨0,0,0,0,0,0,0,0⟩,0,0,0,0,0,0,0,0,0,0,0⟩

def skeleton : Term 0 1 4 := shape (program 0 blank)

/-- Each bind uses its fixed instruction ordinal, so no row address, field
label, original gate table or age parameter is encoded in the ROM. -/
def publicProgram (W : ℕ) : Term W (1+bankSize) 4 :=
  withSlots (fun j => ⟨j%bankSize,Nat.mod_lt _ (by decide)⟩) skeleton 0

/-- The one native scalar parameter is followed by the literal words in
fixed instruction order. The unused bank suffix has value zero. -/
def publicData {W : ℕ} (s : Layout) (original : Fin 1→Word W) : Fin (1+bankSize)→Word W :=
  Fin.append original (fun j => (words (program W s))[j.val]?.getD 0)

theorem publicProgram_eval {W : ℕ} (s : Layout) (original : Fin 1→Word W)
    (m : Memory W) (v : Fin 4→Word W) :
    (publicProgram W).eval (publicData s original) m v=(program W s).eval original m v := by
  have h : (program W s).binds<bankSize := Nat.lt_of_le_of_lt (binds_le W s) (by decide)
  exact correct (C:=bankSize) (program_shape (W:=W) (W':=0) s blank) h original v m

theorem publicProgram_size (W : ℕ) : (publicProgram W).binds≤1000000 := by
  rw [publicProgram,withSlots_binds,skeleton,shape_binds]
  exact binds_le _ _

end ThreeFlat.RAM.TraceBucketAtom

end OAI
