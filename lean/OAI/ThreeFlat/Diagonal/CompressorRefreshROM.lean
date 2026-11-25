import OAI.ThreeFlat.Diagonal.CompressorNativeRefresh
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # The compiled finite port table returns the actual expander permutation -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open scoped Fin.NatCast
variable {w k n D a : ℕ}

private theorem findValue_eq (x y : Word w) (xs : List (Word w × Word w))
    (has : (x,y) ∈ xs) (unique : ∀ z, (x,z) ∈ xs → z=y) : findValue x xs = y := by
  induction xs with
  | nil => simp at has
  | cons p ps ih =>
    rcases p with ⟨q,z⟩
    by_cases h : x=q
    · subst q
      simpa [findValue] using unique z (by simp)
    · rw [findValue,ite_eq_right h]
      apply ih ((List.mem_cons.mp has).resolve_left (fun eq => h (congrArg Prod.fst eq)))
      exact fun v hv => unique v (List.mem_cons_of_mem _ hv)

private theorem bound (p : Fin D × Fin a) : p.1.val*a+p.2.val < D*a := by
  have ht := (finProdFinEquiv p).isLt
  change p.2.val+a*p.1.val < D*a at ht
  simpa [Nat.mul_comm,Nat.add_comm] using ht

theorem portROM_lookup (E : SlotGraph (Fin D) a) (reverse : Bool) (part : Fin D × Fin a → ℕ)
    (fit : D*a ≤ 2^w) (p : Fin D × Fin a) :
    findValue (((p.1.val*a+p.2.val : ℕ) : Word w)) (portROM E reverse part) =
      ((part ((if reverse then E.target.symm else E.target) p)) : Word w) := by
  let enc := fun q : Fin D × Fin a => ((q.1.val*a+q.2.val : ℕ) : Word w)
  let f := fun q : Fin D × Fin a => ((part ((if reverse then E.target.symm else E.target) q)) : Word w)
  have listed (q : Fin D × Fin a) : (enc q,f q) ∈ portROM E reverse part := by
    unfold portROM
    apply List.mem_flatMap.mpr
    exact ⟨q.1,List.mem_finRange _,List.mem_map.mpr ⟨q.2,List.mem_finRange _,rfl⟩⟩
  have inj : Function.Injective enc := by
    intro q r eq
    have h := congrArg Fin.val eq
    simp only [enc,Fin.val_natCast,Nat.mod_eq_of_lt ((bound q).trans_le fit),
      Nat.mod_eq_of_lt ((bound r).trans_le fit)] at h
    apply finProdFinEquiv.injective
    apply Fin.ext
    simpa [Nat.mul_comm,Nat.add_comm] using h
  apply findValue_eq _ _ _ (listed p)
  intro z hz
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hz
  obtain ⟨j,_,he⟩ := List.mem_map.mp hi
  have hkey : enc (i,j) = enc p := congrArg Prod.fst he
  have heq := inj hkey
  exact (congrArg Prod.snd he).symm.trans (congrArg f heq)

theorem eval_port (E : SlotGraph (Fin D) a) (reverse : Bool) (part : Fin D × Fin a → ℕ)
    (fit : D*a ≤ 2^w) (p : Fin D × Fin a) (x : Term w k n)
    (pub : Fin k → Word w) (m : Memory w) (vs : Fin n → Word w)
    (hx : x.eval pub m vs = ((p.1.val*a+p.2.val : ℕ) : Word w)) :
    (findWord x (portROM E reverse part)).eval pub m vs =
      ((part ((if reverse then E.target.symm else E.target) p)) : Word w) := by
  rw [eval_findWord,hx,portROM_lookup E reverse part fit]

end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
