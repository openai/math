import OAI.Hierarchy.ProbeMaskLoop
import OAI.Hierarchy.ProbeStageMask

namespace OAI
/-! # Native scatter of newly forbidden colors into mutable mask words -/

namespace Hierarchy.ProbeStage.MaskUpdate

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Fin.CommRing

abbrev Parameters (w : ℕ) := Fin 5 → Word w

/-- The first three public words address the dynamic count, occurrence-list head, and block mask
base cells. The last two point to the advice arrays of target offsets and bit-clearing words. -/
def parameters (w count head masks offsets clear : ℕ) : Parameters w := ![count,head,masks,offsets,clear]

def step {w : ℕ} (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let j := m (v 1).val + i
  let offset := m (v 3 + j).val
  let dst := m (v 2).val + offset
  let keep := m (v 4 + j).val
  writeMemory m dst (BinaryOp.bitAnd.eval (m dst.val) keep)

def ops : List (Op 6 5) :=
  [.publicWord 2 1, .read 2 2, .binary .add 2 2 0,
   .publicWord 3 3, .binary .add 3 3 2, .read 3 3,
   .publicWord 4 2, .read 4 4, .binary .add 3 4 3,
   .publicWord 4 4, .binary .add 4 4 2, .read 4 4,
   .read 5 3, .binary .bitAnd 5 5 4, .write 3 5, .constant 2 1, .binary .add 0 0 2]

def procedure {w : ℕ} (v : Parameters w) : Procedure w :=
  ⟨4+ops.length,6,5,ProbeMaskLoop.block w ops 0 1 0,v⟩

def image {w : ℕ} (v : Parameters w) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | i+1 => step v (i : Word w) (image v m i)

private theorem row {w r k : ℕ} (reg : Fin 6 ↪ Fin r) (pub : Fin 5 → Fin k)
    (v : Fin k → Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,step (v ∘ pub) (rs (reg 0)) m) ∧
    out (reg 0) = rs (reg 0) + 1 ∧ out (reg 1) = rs (reg 1) := by
  simp [ops,step,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

/-- Running the scatter costs four startup ticks and eighteen per occurrence, regardless of the
number of distinct target words or the other bits already removed from each word. -/
theorem execute {w : ℕ} (v : Parameters w) (m : Memory w) :
    let n := (m (v 0).val).val
    (procedure v).Exec m (image v m n) (4+18*n) := by
  let n := (m (v 0).val).val
  dsimp only
  intro P R K M pc reg pub exit installed data c m₀ entry start
  subst m₀
  change Fin 5 → Fin K at pub
  change Fin 6 ↪ Fin R at reg
  change ∀ i : Fin 5, M.publicData (pub i) = v i at data
  have fields : M.publicData ∘ pub = v := funext data
  have count : image v m 0 (M.publicData (pub 0)).val = (n : Word w) := by
    change m (M.publicData (pub 0)).val = ((m (v 0).val).val : Word w)
    rw [data 0]
    simp
  have run := ProbeMaskLoop.advance_block ops 0 1 (by decide) 0 M pc reg pub exit installed n
    (m (v 0).val).isLt (image v m) count (fun i hi state rs cur bd => by
      obtain ⟨events,out,hs,hcur,hbd⟩ := row reg pub M.publicData state rs (image v m i)
      rw [fields,cur] at hs
      exact ⟨events,out,hs,by simpa [cur,Nat.cast_add] using hcur, hbd.trans bd⟩)
    c entry
  obtain ⟨out,hr,hpc⟩ := run
  have cost : 4+n*(1+ops.length)=4+18*n := by change 4+n*18=4+18*n; rw [Nat.mul_comm n 18]
  exact ⟨_,cost.le,out,_,hr,hpc,rfl⟩

/-- Every advice bit belongs to one color. During a block's monotone scan its first saturation
therefore visits at most `B⁴ ℓ` occurrence descriptors in total. -/
theorem all_occurrences {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (S : Finset (Fin B)) :
    ∑ c ∈ S, (Finset.univ.filter fun p : MaskIndex B × Fin ℓ => strings p.1 p.2=c).card ≤ B^4*ℓ := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (MaskIndex B × Fin ℓ)))
    (t := Finset.univ) (f := fun p => strings p.1 p.2) (fun _ _ => Finset.mem_univ _)
  calc
    _ ≤ ∑ c, (Finset.univ.filter fun p : MaskIndex B × Fin ℓ => strings p.1 p.2=c).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by omega)
    _ = _ := by rw [← h]; simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,MaskIndex]; ring

end Hierarchy.ProbeStage.MaskUpdate

end OAI
