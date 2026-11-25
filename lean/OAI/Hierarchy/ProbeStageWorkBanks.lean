import OAI.Hierarchy.ProbeStageInitial
import OAI.Hierarchy.ProbeRecordInputs

namespace OAI
/-! # The native input, advice, scratch and output banks at every depth -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM

/-- The initial endpoint banks are populated from the input permutation.
Deeper levels use the three middle columns written by the preceding split. -/
def parentAt (h d copies : ℕ) : ℕ → Fin 3 → Bank
  | 0 => ![initialGroup h,initialInput h,initialOutput h]
  | j+1 => ![outputBank (output h d copies j) h 3,outputBank (output h d copies j) h 4,
    outputBank (output h d copies j) h 5]

def rankAt (h d copies j : ℕ) (k : Fin 3) : Bank := ⟨bankBase h d copies j k.val,h⟩
def geometryAt (h d copies j : ℕ) (k : Fin 8) : Bank :=
  ⟨bankBase h d copies j (3+k.val),roomBits h d⟩

def operandsAt (h d copies j : ℕ) : Inputs :=
  ⟨parentAt h d copies j 0,parentAt h d copies j 1,parentAt h d copies j 2,
   rankAt h d copies j 0,rankAt h d copies j 1,rankAt h d copies j 2⟩

def tablesAt (h d copies j : ℕ) : Tables :=
  let g := geometryAt h d copies j
  ⟨g 0,g 1,g 2,g 3,g 4,g 5⟩

def endpointAt (h d copies j : ℕ) : Endpoints :=
  let p := parentAt h d copies j
  let g := geometryAt h d copies j
  ⟨p 0,p 1,p 2,g 0,g 2,g 6,g 7⟩

/-- The allocator reads these three tightly packed columns at the record
ordinal. Their containing area ends before the mask workspace. -/
def allocatorBase (h d copies j : ℕ) := bankBase h d copies j 11

def blockBank (h d copies j : ℕ) (k : Fin 3) : Bank :=
  ⟨allocatorBase h d copies j+k.val*2^h,h⟩

theorem extent_word (h d copies : ℕ) : extent h d<2^wordBits h d copies := by
  apply lt_of_le_of_lt _ (heap_room h d copies)
  apply Nat.le_mul_of_pos_left
  omega

theorem height_extent (h d : ℕ) : 2^h≤extent h d :=
  Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)

theorem parent_end (h d copies j : ℕ) (k : Fin 3) :
    (parentAt h d copies j k).base + (parentAt h d copies j k).size ≤ phase h d copies j := by
  have hroom := height_extent h d
  cases j with
  | zero =>
    fin_cases k <;> simp [parentAt,initialGroup,initialInput,initialOutput,Bank.size,phase] <;> omega
  | succ j =>
    have hi := output_end h d copies j
    fin_cases k <;> simp [parentAt,outputBank,Bank.size] <;> omega

private theorem parent_fit (h d copies j out : ℕ) (hp : phase h d copies j≤out) (k : Fin 3) :
    (parentAt h d copies j k).Fits (wordBits h d copies) out := by
  have hroom := (height_extent h d).trans_lt (extent_word h d copies)
  have sz : (parentAt h d copies j k).size=2^h := by
    cases j <;> fin_cases k <;> rfl
  exact ⟨by rw [sz];exact Nat.two_pow_pos h,by rw [sz];exact hroom,(parent_end ..).trans hp⟩

private theorem geometry_fit {h d copies j t : ℕ} (k : Fin 8) (before : 3+k.val<t) :
    (geometryAt h d copies j k).Fits (wordBits h d copies) (bankBase h d copies j t) :=
  ⟨Nat.two_pow_pos _,extent_word ..,separate h d copies j _ _ before⟩

private theorem rank_fit {h d copies j t : ℕ} (k : Fin 3) (before : k.val<t) :
    (rankAt h d copies j k).Fits (wordBits h d copies) (bankBase h d copies j t) :=
  ⟨Nat.two_pow_pos _,(height_extent h d).trans_lt (extent_word ..),
    (Nat.add_le_add_left (height_extent h d) _).trans (separate h d copies j _ _ before)⟩

theorem endpoint_fits (h d copies j : ℕ) (i : Fin 3) :
    ((endpointAt h d copies j).term i).Fits (wordBits h d copies) (allocatorBase h d copies j) := by
  have parents := parent_fit h d copies j (allocatorBase h d copies j)
    (Nat.le_add_right _ _)
  have fixed (k : Fin 8) : (geometryAt h d copies j k).Fits (wordBits h d copies) (allocatorBase h d copies j) :=
    geometry_fit k (by omega)
  fin_cases i <;> simp [endpointAt,Endpoints.term,rowAdd,rowCell,Expr.Fits,parents,fixed]

theorem operands_fit (h d copies j : ℕ) (i : Fin 9) :
    (field (operandsAt h d copies j) (tablesAt h d copies j) i).Fits
      (wordBits h d copies) (output h d copies j) := by
  have big : 23 ≤ stride d copies-9 := by unfold stride;omega
  have parents := parent_fit h d copies j (output h d copies j) (Nat.le_add_right _ _)
  have fixed (k : Fin 8) : (geometryAt h d copies j k).Fits (wordBits h d copies) (output h d copies j) :=
    geometry_fit k (by omega)
  have ranks (k : Fin 3) : (rankAt h d copies j k).Fits (wordBits h d copies) (output h d copies j) :=
    rank_fit k (by omega)
  fin_cases i <;> simp [field,operandsAt,tablesAt,rowAdd,rowCell,Expr.Fits,parents,fixed,ranks]

theorem allocator_end (h d copies j : ℕ) :
    allocatorBase h d copies j+3*2^h ≤ bankBase h d copies j 14 := by
  have hroom := Nat.mul_le_mul_left 3 (height_extent h d)
  unfold allocatorBase bankBase
  omega

end Hierarchy.ProbeStage.Native

end OAI
