import OAI.Computability.NearSquareRoot.KernelScaleIndex
import OAI.Computability.NearSquareRoot.KernelScaleRecord
import OAI.Computability.NearSquareRoot.KernelScaleSpectator
import OAI.Computability.NearSquareRoot.KernelPassMixBanks
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # Applying the normalized scale pass to one physical row bank

Leading spectator positions repeat the whole table, and trailing positions
repeat each table entry. The records for different spectator positions are
independent. At each address a finite tag selects a fixed dyadic operation on
one complex record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleBank
open IntegerMultiplication Code KernelPass
open KernelScaleStream (singleColumns tag tagTask tag_singleColumns)
open KernelScaleSpectator (expand)

/-- The labels used to state the semantics may include independent spectators.
The machine receives the three unary shape parameters and the bank. -/
structure Layout (a : ℕ) (I F : Type) where
  h : I → ℕ
  prefixCount : I → ℕ
  suffixCount : I → ℕ
  prefix_pos : ∀ i, 0 < prefixCount i
  suffix_pos : ∀ i, 0 < suffixCount i
  rows : I → List F
  coord : (i : I) → F → Addr (a+1) (h i)
  address_order : ∀ i, (rows i).map (fun z => singleColumns (List.ofFn (coord i z))) =
    expand (prefixCount i) (suffixCount i) (KernelSelector.addressColumns a (2*h i))

variable {a q : ℕ} {I F : Type} (L : Layout a I F)

def width (i : I) := (a+1)*(2*L.h i)

def header (i : I) := ((tally (L.prefixCount i), tally (L.suffixCount i)), tally (width L i))

theorem count_eq (i : I) : (L.rows i).length = L.prefixCount i *
    (2^(width L i) * L.suffixCount i) := by
  simpa [width, KernelSelector.addressColumns] using congrArg List.length (L.address_order i)

def signature (test : Column (a+1) → Fin q → ZMod 2) (i : I) (z : F) :
    Fin q → ZMod 2 := ∑ j, test (L.coord i z j)

private def tags (test : Column (a+1) → Fin q → ZMod 2) (i : I) :=
  (KernelSelector.addressColumns a (2*L.h i)).map (tag test)

private theorem tag_order (test : Column (a+1) → Fin q → ZMod 2) (i : I) :
    expand (L.prefixCount i) (L.suffixCount i) (tags L test i) =
      (L.rows i).map (fun z => finFunctionFinEquiv (signature L test i z)) := by
  rw [tags, ← KernelScaleSpectator.map_expand, ← L.address_order, List.map_map]
  apply List.map_congr_left
  intro z _
  exact (Equiv.symm_apply_eq ..).mp (tag_singleColumns test (L.coord i z))

/-- A normalized scale pass has precisely one work row. -/
def bank {w : I → ℕ} (x : (i : I) → F → Dusk.Grain (w i)) (i : I) :=
  [(L.rows i).map (fun z => Dusk.mark (x i z))]

private theorem list_vol {X Y : Type} [Codec Y] (l : List X) (f : X → Y) (B : ℕ)
    (h : ∀ z, size (f z)+1 ≤ B) : size (l.map f) ≤ B*l.length+1 := by
  induction l with
  | nil => simp
  | cons z l ih => specialize h z; simp only [List.map_cons, size_cons, List.length_cons, Nat.mul_succ]; omega

private def tagUnit (q : ℕ) := 2*2^q+2

private theorem tag_size (q : ℕ) (j : Fin (2^q)) : size j+1 ≤ tagUnit q := by
  change size (tally j.val) + 1 ≤ _
  simp only [size_tally, tally_length, tagUnit]
  omega

private theorem bank_size {w : I → ℕ} (x : (i : I) → F → Dusk.Grain (w i)) (i : I) :
    size (bank L x i) ≤ (4*(w i+1)+4)*(L.rows i).length+3 := by
  have vol := list_vol (L.rows i) (fun z => Dusk.mark (x i z)) (4*(w i+1)+4)
    (fun _ => by rw [Dusk.volume])
  simp only [bank, size_cons, size_nil]
  omega

private theorem bounds (i : I) :
    let N := (L.rows i).length
    2^(width L i) ≤ N ∧ L.prefixCount i ≤ N ∧ L.suffixCount i ≤ N ∧
      L.prefixCount i * L.suffixCount i ≤ N := by
  rw [count_eq]
  dsimp only
  have hN : 0 < 2^(width L i) := pow_pos (by decide) _
  have p := L.prefix_pos i
  have s := L.suffix_pos i
  have h₁ := Nat.le_mul_of_pos_right (2^(width L i)) s
  have h₂ := Nat.le_mul_of_pos_left (2^(width L i) * L.suffixCount i) p
  have h₃ := Nat.le_mul_of_pos_left (L.suffixCount i) hN
  exact ⟨h₁.trans h₂, Nat.le_mul_of_pos_right _ (by positivity), h₃.trans h₂, Nat.mul_le_mul_left _ h₃⟩

private def finish {q : ℕ} (table : (Fin q → ZMod 2) → Coefficient)
    (s : List (Fin (2^q)) × List (List Dusk.Pair)) : List (List Dusk.Pair) :=
  [(zipFair 0 ([],[]) (s.1,s.2.headD [])).map fun u =>
    KernelScaleRecord.applyCoeff (table (finFunctionFinEquiv.symm u.1)) u.2]

private theorem easy_finish (table : (Fin q → ZMod 2) → Coefficient) : Easy (finish table) := by
  have zip := (Easy.fst.pair (Easy.snd.compose (Iter.leader ([] : List Dusk.Pair)))).compose
    (easy_zip (0 : Fin (2^q)) (([],[]) : Dusk.Pair))
  have act := zip.compose (KernelScaleRecord.easy_select (fun j => table (finFunctionFinEquiv.symm j))).mapping
  exact (act.pair (Easy.const [])).compose Easy.cons

/-- One fixed command takes a shape header and a single bank, computes the
finite tag at every address, and performs every indicated signed dyadic scale.
The work is linear in the bank size plus the address bits generated. -/
private theorem scaleBankTo (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i))
    (y : (i : I) → F → Dusk.Grain (w i))
    (ok : ∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.applyCoeff (table (signature L test i z))
      (Dusk.mark (x i z)) = Dusk.mark (y i z)) :
    Task (fun i => (L.rows i).length * (width L i+w i+1))
      (fun i => send (header L i, bank L x i))
      (fun i => send (bank L y i)) := by
  let ns (i : I) := (tally (L.prefixCount i), tally (L.suffixCount i))
  let big (i : I) := expand (L.prefixCount i) (L.suffixCount i) (tags L test i)
  have gen := (KernelSelector.generateColumnTable _ (tagTask test)).on (fun i => 2*L.h i)
  have ex := (KernelScaleSpectator.expandPositive L.prefixCount L.suffixCount (tags L test)
    L.prefix_pos L.suffix_pos)
  have A := ((gen.right (fun i => send (ns i))).compose ex).left (fun i => send (bank L x i))
  have B := (easy_finish table).on (fun i => (big i, bank L x i))
  have ends (i : I) : finish table (big i, bank L x i) =
      bank L y i := by
    simp only [finish, big, tag_order, bank, List.headD_cons, fair, List.map_map, Function.comp_def]
    apply congrArg (fun u => [u])
    apply List.map_congr_left
    intro z hz
    rw [show finFunctionFinEquiv.symm (finFunctionFinEquiv (signature L test i z)) =
      signature L test i z from Equiv.symm_apply_apply finFunctionFinEquiv _]
    exact ok _ _ hz
  simp only [ends] at B
  apply (A.compose B).bound (2*tagUnit q + 32)
  intro i
  obtain ⟨hN,hP,hS,hPS⟩ := bounds L i
  have hW := Nat.mul_le_mul_right (width L i+1) hN
  have sz := KernelScaleSpectator.size_expand (L.prefixCount i) (L.suffixCount i) (tags L test i)
  have tt : size (big i) ≤ tagUnit q * (L.rows i).length + 1 := by
    dsimp only [big]
    rw [tag_order]
    exact list_vol _ _ _ (fun _ => tag_size q _)
  have bb := bank_size L x i
  change size (ns i) + (width L i+1)*2^(width L i) +
    L.prefixCount i * L.suffixCount i * size (tags L test i) +
    size (big i,bank L x i) + 1 ≤ _
  change size (big i) + _ = _ at sz
  simp only [ns, size_prod, size_tally, tally_length]
  let V := (L.rows i).length * (width L i+w i+1)
  have rowV : (L.rows i).length ≤ V := Nat.le_mul_of_pos_right _ (by omega)
  have wV : (L.rows i).length * (w i+1) ≤ V := Nat.mul_le_mul_left _ (by omega)
  have gV : (width L i+1)*2^(width L i) ≤ V := by
    rw [Nat.mul_comm]
    exact hW.trans (Nat.mul_le_mul_left _ (by omega))
  have tV := Nat.mul_le_mul_left (tagUnit q) rowV
  have bV : size (bank L x i) ≤ 4*V + 4*V + 3 := by nlinarith only [bb,wV,rowV]
  change _ ≤ (2*tagUnit q+32)*(V+1)
  nlinarith only [tV,tt,sz,bV,gV,rowV,hP,hS,hPS]

/-- With headroom the selected complex multiplication returns the rounded
mathematical output at every address. -/
theorem scaleBank (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i))
    (room : ∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.fits (table (signature L test i z)) (x i z)) :
    Task (fun i => (L.rows i).length * (width L i+w i+1))
      (fun i => send (header L i, bank L x i))
      (fun i => send (bank L (fun t z => KernelScaleRecord.rounded (table (signature L test t z)) (x t z)) i)) :=
  scaleBankTo L test table w x _ (fun i z hz => KernelScaleRecord.applyCoeff_mark _ _ (room i z hz))

def volume (w : I → ℕ) (i : I) := (L.rows i).length * (width L i+w i+1)

private theorem header_size (w : I → ℕ) (i : I) :
    size (header L i) ≤ 6 * volume L w i + 5 := by
  obtain ⟨n,p,s,_⟩ := bounds L i
  have u : (L.rows i).length ≤ volume L w i := Nat.le_mul_of_pos_right _ (by omega)
  have hu : width L i ≤ 2^(width L i) := (Nat.lt_two_pow_self).le
  simp only [header, size_prod, size_tally, tally_length]
  omega

private theorem bank_volume (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i)) (i : I) :
    size (bank L x i) ≤ 8*volume L w i + 3 := by
  have h := bank_size L x i
  have u : (L.rows i).length ≤ volume L w i := Nat.le_mul_of_pos_right _ (by omega)
  have v : (L.rows i).length * (w i+1) ≤ volume L w i := Nat.mul_le_mul_left _ (by omega)
  nlinarith only [h,u,v]

def output {w : I → ℕ} (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (x : (i : I) → F → Dusk.Grain (w i)) (i : I) :=
  bank L (fun t z => KernelScaleRecord.rounded (table (signature L test t z)) (x t z)) i

theorem scaleBank_header (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i))
    (room : ∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.fits (table (signature L test i z)) (x i z)) :
    Task (volume L w) (fun i => send (header L i, bank L x i))
      (fun i => send (header L i, output L test table x i)) := by
  have run := KernelPassMixBanks.preserveHeader (fun i => send (header L i)) _ _ _
    (scaleBank L test table w x room)
  apply run.bound 10
  intro i
  change size (header L i) + volume L w i + 1 ≤ _
  have hh := header_size L w i
  omega

/-- The scale primitive fits in linear space on top of an arbitrary parked
stack frame; the header survives for the next pass. -/
theorem scaleBank_bounded (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i))
    (room : ∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.fits (table (signature L test i z)) (x i z)) :
    Space.BoundedTask (volume L w) (volume L w) (fun i => send (header L i, bank L x i))
      (fun i => send (header L i, output L test table x i)) := by
  apply (Space.BoundedTask.of_time (scaleBank_header L test table w x room)).bound 1 20
  · simp
  · intro i
    have hh := header_size L w i
    have hr := bank_volume L w x i
    change size (header L i) + size (bank L x i) + 1 + volume L w i + 1 ≤ _
    omega

theorem physical_scaleBank (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i))
    (room : ∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.fits (table (signature L test i z)) (x i z)) :
    ShortWord.PhysicalTask (volume L w) (fun i => send (header L i, bank L x i))
      (fun i => send (header L i, output L test table x i)) :=
  ShortWord.physicalTask (scaleBank_header L test table w x room)

/-- The total scale command as a leaf of the physical grammar, on every bit
pattern. It computes the packed output even when a supplied row overflows. -/
theorem storedBank_bounded (test : Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (w : I → ℕ) (x : (i : I) → F → Dusk.Grain (w i)) :
    Space.BoundedTask (volume L w) (volume L w) (fun i => send (header L i, bank L x i))
      (fun i => send (header L i,
        bank L (fun t z => KernelScaleRecord.stored (table (signature L test t z)) (x t z)) i)) := by
  have task := scaleBankTo L test table w x _ (fun _ _ _ => KernelScaleRecord.applyCoeff_stored _ _)
  have hdr := KernelPassMixBanks.preserveHeader (fun i => send (header L i)) _ _ _ task
  apply (Space.BoundedTask.of_time hdr).bound 10 27
  · intro i
    change size (header L i) + volume L w i + 1 ≤ _
    have hh := header_size L w i
    omega
  · intro i
    have hh := header_size L w i
    have hr := bank_volume L w x i
    change size (header L i) + size (bank L x i) + 1 +
      (size (header L i) + volume L w i) + 1 ≤ _
    omega

/-- The scale matrix acts by a single product at each ideal address. -/
theorem scale_mulVec {A h : ℕ} (test : Column A → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (v : Fin 1 × Addr A h → ℂ) (z : Addr A h) :
    Matrix.mulVec (((Plan.scale q test table).eval h).map (fun t => (t : ℂ))) v (0,z) =
      (value (table (∑ j, test (z j))) : ℂ) * v (0,z) := by
  classical
  change (∑ y : Fin 1 × Addr A h, ((if y.2 = z then value (table (∑ j, test (y.2 j))) else 0 : ℚ) : ℂ)
    * v y) = _
  rw [Finset.sum_eq_single (0,z)]
  · simp
  · intro y _ hy
    have e : y.2 ≠ z := fun he => hy (Prod.ext (Subsingleton.elim _ _) he)
    simp [e]
  · simp

end KernelScaleBank

end NearSquareRoot
end Computability
end OAI
