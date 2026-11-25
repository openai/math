import OAI.Hierarchy.DescentEpochTagKeys
import OAI.Hierarchy.DescentBundleScalar

namespace OAI
/-! # Terminal codes for grouped affine slices of a bundled physical cable

There is one bounded length digit per original operand, and one triple of
bounded integers per physical slice. The sum of the operand lengths tells
the decoder exactly how many triples belong to the term.
-/
namespace Hierarchy.DescentBundleTagKeys
open DescentEpochTagKeys DescentBundleHistory

private def natKey (n : ℕ) : Codec ℕ (n+1) where
  store x := ⟨min n x, Nat.lt_succ_of_le (min_le_left ..)⟩
  read x := x.val
  fits x := x≤n
  read_store _x h := min_eq_right h

def radix (p R : ℕ) := (p+1)*((R+2)*(R+2))

def SliceFits (p R : ℕ) (s : SliceCode) : Prop :=
  s.start≤p ∧ s.stride≤R ∧ s.count≤R+1

def slice (p R : ℕ) : Codec SliceCode (radix p R) :=
  let book := (natKey p).prod ((natKey (R+1)).prod (natKey (R+1)))
  { store := fun s => book.store (s.start,s.stride,s.count)
    read := fun i => let z := book.read i; ⟨z.1,z.2.1,z.2.2⟩
    fits := SliceFits p R
    read_store := by
      rintro ⟨start,stride,count⟩ ⟨startFits,strideFits,countFits⟩
      have ok : book.fits (start,stride,count) := ⟨startFits,Nat.le_succ_of_le strideFits,countFits⟩
      rw [book.read_store _ ok] }

private def putSlots (p R G : ℕ) (xs : List SliceCode) (i : Fin G) : Fin (radix p R) :=
  if h : i.val<xs.length then (slice p R).store xs[i.val] else (slice p R).store ⟨0,0,0⟩

private def getSlots (p R G k : ℕ) (slots : Fin G → Fin (radix p R)) : List SliceCode :=
  List.ofFn fun i : Fin (min G k) =>
    (slice p R).read (slots ⟨i.val, i.isLt.trans_le (min_le_left ..)⟩)

private theorem slots_back (p R G : ℕ) (xs : List SliceCode) (length : xs.length≤G)
    (ok : ∀ s∈xs, SliceFits p R s) :
    getSlots p R G xs.length (putSlots p R G xs) = xs := by
  apply List.ext_getElem
  · simp [getSlots,min_eq_right length]
  · intro i hi hx
    have good := ok xs[i] (List.getElem_mem hx)
    simp only [getSlots,List.getElem_ofFn]
    change (slice p R).read (putSlots p R G xs ⟨i,_⟩)=xs[i]
    rw [putSlots,dite_eq_left hx]
    exact (slice p R).read_store _ good

private theorem sum_lengths {α : Type*} (rows : List (List α)) :
    (rows.map List.length).sum = rows.flatten.length := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change r.length+(rs.map List.length).sum=(r++rs.flatten).length
    rw [List.length_append,ih]

private theorem length_member {α : Type*} {r : List α} (rows : List (List α)) (hr : r∈rows) :
    r.length≤rows.flatten.length := by
  induction rows with
  | nil => simp at hr
  | cons head tail ih =>
    rcases List.mem_cons.mp hr with eq|mem
    · subst r; simp
    · have := ih mem
      simp only [List.flatten_cons,List.length_append]
      omega

def capacity (n A G p R : ℕ) := (n*span A G)*(radix p R)^G

def Fits {U : Type*} {n : ℕ} (old : Codec U n) (A G p R : ℕ)
    (t : U × List (List SliceCode)) :=
  old.fits t.1 ∧ t.2.length≤A ∧ t.2.flatten.length≤G ∧ ∀ s∈t.2.flatten, SliceFits p R s

/-- Encode the printed scalar name, the length of each original operand's
slice list, and the genuine affine charts in their physical order. -/
def codec {U : Type*} {n : ℕ} (old : Codec U n) (A G p R : ℕ) :
    Codec (U × List (List SliceCode)) (capacity n A G p R) :=
  let book := (old.pieces A G).prod
    (Codec.ofEquiv (finFunctionFinEquiv : (Fin G → Fin (radix p R)) ≃ Fin ((radix p R)^G)))
  { store := fun t => book.store ((t.1,t.2.map List.length),putSlots p R G t.2.flatten)
    read := fun i => let z := book.read i
                     (z.1.1,z.1.2.splitLengths (getSlots p R G z.1.2.sum z.2))
    fits := Fits old A G p R
    read_store := by
      rintro ⟨t,rows⟩ ⟨oldFit,arity,flatLen,allFit⟩
      have sizes : ListFits A G (rows.map List.length) := by
        constructor
        · simpa using arity
        · intro x h
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
          exact (length_member rows hr).trans flatLen
      have valid : book.fits ((t,rows.map List.length),putSlots p R G rows.flatten) :=
        ⟨⟨oldFit,sizes⟩,trivial⟩
      dsimp only
      rw [book.read_store _ valid,sum_lengths,
        slots_back p R G rows.flatten flatLen allFit,regroup] }

/-- The compiled scalar reads the same printed tag and operand bits after
writing and reading its compact terminal key. -/
theorem value {U K : Type} {n : ℕ} (old : Codec U n) (A G p R : ℕ)
    (dict : U→List (List Bool)→K) (t : U × List (List SliceCode)) (fit : Fits old A G p R t)
    (words : List (List Bool)) :
    let book := codec old A G p R
    bundleScalar p dict (book.read (book.store t)) words=bundleScalar p dict t words := by
  dsimp only
  rw [(codec old A G p R).read_store _ fit]

def width (tagBits A G p R : ℕ) := tagBits + Nat.clog 2 (A+1) + A*Nat.clog 2 (G+1) +
    G*(Nat.clog 2 (p+1)+2*Nat.clog 2 (R+2))

theorem code_width (n tagBits A G p R : ℕ) (tag : n≤2^tagBits) :
    Nat.clog 2 (capacity n A G p R) ≤ width tagBits A G p R := by
  have two : 1<2 := by decide
  have marks : span A G ≤ 2^(Nat.clog 2 (A+1)+A*Nat.clog 2 (G+1)) := calc
    _ ≤ 2^(Nat.clog 2 (A+1)) * (2^(Nat.clog 2 (G+1)))^A :=
      Nat.mul_le_mul (Nat.le_pow_clog two _) (Nat.pow_le_pow_left (Nat.le_pow_clog two _) A)
    _ = _ := by rw [←pow_mul,←pow_add]; congr 1; ring
  have triples : radix p R ≤ 2^(Nat.clog 2 (p+1)+2*Nat.clog 2 (R+2)) := calc
    _ ≤ 2^(Nat.clog 2 (p+1)) * (2^(Nat.clog 2 (R+2)) * 2^(Nat.clog 2 (R+2))) :=
      Nat.mul_le_mul (Nat.le_pow_clog two _) (Nat.mul_le_mul (Nat.le_pow_clog two _) (Nat.le_pow_clog two _))
    _ = _ := by rw [←pow_add,←pow_add]; congr 1; ring
  apply (Nat.clog_le_iff_le_pow two).2
  calc
    _ ≤ (2^tagBits * 2^(Nat.clog 2 (A+1)+A*Nat.clog 2 (G+1))) *
        (2^(Nat.clog 2 (p+1)+2*Nat.clog 2 (R+2)))^G :=
      Nat.mul_le_mul (Nat.mul_le_mul tag marks) (Nat.pow_le_pow_left triples G)
    _ = _ := by rw [←pow_mul,←pow_add,←pow_add]; congr 1; unfold width; ring

theorem code_width_of_arity_le (n tagBits A G p R : ℕ) (tag : n≤2^tagBits) (arity : A≤G) :
    Nat.clog 2 (capacity n A G p R) ≤ tagBits+(A+1)*Nat.clog 2 (G+1)+
      G*(Nat.clog 2 (p+1)+2*Nat.clog 2 (R+2)) := by
  have head := Nat.clog_mono_right 2 (Nat.add_le_add_right arity 1)
  apply (code_width n tagBits A G p R tag).trans
  unfold width
  rw [Nat.add_mul,Nat.one_mul]
  omega

end Hierarchy.DescentBundleTagKeys

end OAI
