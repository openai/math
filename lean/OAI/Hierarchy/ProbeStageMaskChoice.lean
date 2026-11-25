import OAI.Hierarchy.ProbeStagePackedMasks
import OAI.Hierarchy.ProbeStageLeast

namespace OAI
/-! # Consecutive packed chunks return the actual least free candidate position -/

namespace Hierarchy.ProbeStage.PackedMask
open Finset

def findWord (width sentinel : ℕ) (get : ℕ → ℕ) : List ℕ → ℕ
  | [] => sentinel
  | k::ks => if get k=0 then findWord width sentinel get ks else k*width + MaskWords.least (get k)

theorem findWord_hit (width sentinel : ℕ) (get : ℕ → ℕ) (k : ℕ) (ks : List ℕ)
    (ordered : ks.Pairwise (· < ·)) (here : k∈ks) (positive : get k≠0) (prior : ∀ j<k,get j=0) :
    findWord width sentinel get ks=k*width+MaskWords.least (get k) := by
  induction ks with
  | nil => simp at here
  | cons a ks ih =>
    by_cases h : a=k
    · subst a; simp [findWord,positive]
    · have mem := (List.mem_cons.mp here).resolve_left (Ne.symm h)
      have lt := (List.pairwise_cons.mp ordered).1 _ mem
      simpa [findWord,prior a lt] using ih (List.pairwise_cons.mp ordered).2 mem

theorem findWord_empty (width sentinel : ℕ) (get : ℕ → ℕ) (ks : List ℕ) (none : ∀ k∈ks,get k=0) :
    findWord width sentinel get ks=sentinel := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa [findWord,none k (by simp)] using ih (fun a ha=>none a (by simp [ha]))

theorem and_word {B ℓ : ℕ} (r : Fin ℓ → Fin B) (L R : Finset (Fin B)) (width k : ℕ) :
    (word r L width k &&& word r R width k)=word r (L∪R) width k := by
  apply Nat.eq_of_testBit_eq
  intro t
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_and,Bool.and_eq_true,word_test,Finset.mem_union,not_or]
  constructor
  · rintro ⟨⟨ht,i,hi,hL⟩,_,j,hj,hR⟩
    have same : i=j := Fin.ext (hi.trans hj.symm)
    subst j
    exact ⟨ht,i,hi,hL,hR⟩
  · rintro ⟨ht,i,hi,hL,hR⟩
    exact ⟨⟨ht,i,hi,hL⟩,ht,i,hi,hR⟩

def firstIndex {B ℓ : ℕ} (row : Fin ℓ → Fin B) (good : Finset (Fin B)) :=
  let bits := freeBits row good
  if h : bits.Nonempty then (bits.min' h).val else ℓ

theorem find_prescribed {B ℓ : ℕ} (row : Fin ℓ → Fin B) (full good : Finset (Fin B))
    (avail : ∀ c, c∈good ↔ c∉full) (width chunks : ℕ) (positive : 0<width) (room : ℓ≤chunks*width) :
    findWord width ℓ (word row full width) (List.range chunks)=firstIndex row good := by
  let bits := freeBits row good
  have mem (i : Fin ℓ) : i∈bits ↔ row i∉full := by simp [bits,freeBits,avail]
  by_cases h : bits.Nonempty
  · let i := bits.min' h
    have goodi := (mem i).mp (min'_mem bits h)
    have low (j : Fin ℓ) (hj : row j∉full) : i.val≤j.val := min'_le bits _ ((mem j).mpr hj)
    let k := i.val/width
    let t := i.val%width
    have rem : t<width := Nat.mod_lt _ positive
    have div : k*width+t=i.val := by simpa [k,t,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div i.val width
    have hit : (word row full width k).testBit t = true := (word_test ..).mpr ⟨rem,i,div.symm,goodi⟩
    have hk : word row full width k≠0 := by intro e; simp [e] at hit
    have least := MaskWords.least_spec hk
    obtain ⟨_,j,hj,hfree⟩ := (word_test ..).mp least.1
    have lt := least.2 t hit
    have ge := low j hfree
    have lea : MaskWords.least (word row full width k)=t := by omega
    have kmem : k∈List.range chunks := List.mem_range.mpr ((Nat.div_lt_iff_lt_mul positive).mpr (i.isLt.trans_le room))
    have prior (u : ℕ) (hu : u<k) : word row full width u=0 := by
      by_contra hn
      obtain ⟨bound,z,hz,hf⟩ := (word_test ..).mp (MaskWords.least_spec hn).1
      have le := low z hf
      have mul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hu)
      rw [Nat.succ_mul] at mul
      omega
    rw [findWord_hit _ _ _ k _ List.pairwise_lt_range kmem hk prior,lea,div]
    simp only [firstIndex,←show bits=freeBits row good from rfl,dite_eq_left h,i]
  · have none (u : ℕ) : word row full width u=0 := by
      by_contra hn
      obtain ⟨_,z,_,hf⟩ := (word_test ..).mp (MaskWords.least_spec hn).1
      exact h ⟨z,(mem z).mpr hf⟩
    rw [findWord_empty _ _ _ _ (fun x _=>none x)]
    simp only [firstIndex,←show bits=freeBits row good from rfl,dite_eq_right h]

end Hierarchy.ProbeStage.PackedMask

end OAI
