import OAI.Hierarchy.ProbeStageHistory
import OAI.Hierarchy.ProbeStageLocations
import OAI.Hierarchy.ProbeStageTape
import OAI.Hierarchy.ProbeStagePrefixLoads

namespace OAI
/-! # Contents of the two true mutable count and mask regions -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing
noncomputable section

theorem initialPacked_at {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B)
    (width chunks b : ℕ) (r : MaskIndex B) (k : Fin chunks) :
    initialPacked strings width chunks (b*(B^4*chunks)+rowCode r*chunks+k.val)=
      PackedMask.word (strings r) ∅ width k.val := by
  have cp : 0<chunks := Nat.zero_lt_of_lt k.isLt
  have rb := rowCode_lt r
  have pos : 0<B^4 := Nat.zero_lt_of_lt rb
  have code : B^2*B^2=B^4 := by ring
  have loc : b*(B^4*chunks)+rowCode r*chunks+k.val=(b*B^4+rowCode r)*chunks+k.val := by ring
  have div : ((b*B^4+rowCode r)*chunks+k.val)/chunks=b*B^4+rowCode r := by
    rw [Nat.mul_comm (b*B^4+rowCode r) chunks,Nat.mul_add_div cp,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  rw [initialPacked,loc,div,code]
  simp [Nat.add_mod,Nat.mod_eq_of_lt rb,Nat.mod_eq_of_lt k.isLt,readRow_at]

def allArrays (h d w : ℕ) (j : Fin (rounds d)) (m : Memory w) : Prop :=
  ∀ (k : Fin 16) (i : ℕ), i<regionSize h d →
    m (region h d j.val k+i)=(arrayValue h d j.val k i : Word w)

def immutable (h d w : ℕ) (j : Fin (rounds d)) (m : Memory w) : Prop :=
  ∀ (k : Fin 12) (i : ℕ), i<regionSize h d →
    m (region h d j.val ⟨k.val,by omega⟩+i)=(arrayValue h d j.val ⟨k.val,by omega⟩ i : Word w)

theorem allArrays_tape (h d w : ℕ) (j : Fin (rounds d)) (m : Memory w) :
    allArrays h d w j (inputTape h d w m) :=
  fun k i hi => inputTape_array m (⟨j,k,⟨i,hi⟩⟩ : ArrayCell h d)

theorem allArrays.immutable {h d w : ℕ} {j : Fin (rounds d)} {m : Memory w} (all : allArrays h d w j m) :
    immutable h d w j m := fun _k i hi => all _ i hi

/-- Number the pair (parent group, block) by the immutable mixed-radix
encoding used in the endpoint pass. -/
def blockNumber {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (π : Equiv.Perm (Fin (2^h)))
    (b : (history h d π j.val).shape.Group × Fin (blocks (history h d π j.val).shape.span (radix h d))) :
    Fin (groupBlocks h d j.val) :=
  ⟨(finProdFinEquiv ((history h d π j.val).encode b.1,b.2)).val,by
    have bound := (finProdFinEquiv ((history h d π j.val).encode b.1,b.2)).isLt
    have dims := history_sizes hd π j.isLt.le
    unfold groupBlocks
    simpa only [← dims.1,← dims.2] using bound⟩

def endpointKey {h d : ℕ} (j : Fin (rounds d)) (π : Equiv.Perm (Fin (2^h))) (left : Bool) :=
  let p := (history h d π j.val).tiles
  if left then leftBlock p (radix_pos h d) else rightBlock p (radix_pos h d)

def assigned {h d : ℕ} (j : Fin (rounds d)) (π : Equiv.Perm (Fin (2^h))) :=
  allocateMasked (history h d π j.val).tiles (radix_pos h d) (formatAdvice h d).row

/-- The native data at the beginning of ordinal k consists of the exact
earlier-record counts and the packed bits for colors still available. -/
def PrefixState {h d w : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d))
    (k : ℕ) (m : Memory w) : Prop := by
  classical
  exact (∀ left b c, m (counterLocation h d j.val left (blockNumber hd j π b) c)=
      (Greedy.prefixCount (endpointKey j π left) (assigned j π).color k b c : Word w)) ∧
    ∀ left b r chunk, m (maskLocation h d j.val left (blockNumber hd j π b) r chunk)=
      (PackedMask.word ((formatAdvice h d).row r)
        (Greedy.prefixFull (endpointKey j π left) (assigned j π).color k b) (fieldWidth h) chunk.val : Word w)

theorem initial_prefix {h d w : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (m : Memory w)
    (all : allArrays h d w j m) : PrefixState hd π j 0 m := by
  classical
  constructor
  · intro left b c
    let b' := blockNumber hd j π b
    have cell := all (countArea left) _ (count_offset hd j.isLt.le b' c)
    have no : Greedy.prefixCount (endpointKey j π left) (assigned j π).color 0 b c=0 :=
      Greedy.prefix_zero ..
    rw [no]
    cases left <;> simpa [counterLocation,countArea,arrayValue,Nat.add_assoc,b'] using cell
  · intro left b r chunk
    let b' := blockNumber hd j π b
    have cell := all (maskArea left) _ (mask_offset hd j.isLt.le b' r chunk)
    have none : Greedy.prefixFull (endpointKey j π left) (assigned j π).color 0 b=∅ := by
      ext c
      simp [Greedy.prefixFull,Greedy.prefix_zero,quota,(radix_pos h d).ne']
    rw [none]
    cases left <;> simp [maskArea,arrayValue] at cell <;>
      rw [initialPacked_at] at cell <;>
      simpa [maskLocation,maskArea,Nat.add_assoc,b'] using cell

end
end Hierarchy.ProbeStage.Native

end OAI
