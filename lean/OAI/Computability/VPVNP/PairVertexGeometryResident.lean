import OAI.Computability.VPVNP.PairVertexGeometryRun

/-! # The DFS stack and immutable leaf inputs after vertex initialization -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexGeometry.Ready

open BurstRAM PrivateRAM LiveProgram VertexImage DFS NodeArguments LeafSourceLoad
open scoped Fin.CommRing

variable {c : Constants} {degree a b p r w : ℕ} {rootFields leaf shrink refresh : Segment}
  {A : VertexImage.Placement (segments (segment c degree a b) rootFields leaf shrink refresh) p r}
  {m : Memory w} {pub : Fin 11 → Word w} {st out : Config w p r} {vals : Static 34 → Word w}
  (h : Ready c degree a b A m pub st out vals)

local notation "R" => NativeFrame.fromHeader degree pub (st.reg (A.saved header)) m
local notation "G" => NativeFrame.frameBase R

include h in
theorem stack {top : ℕ} {xs : List (Word w)} (represented : Represents st.privateMem top xs)
    (ends : top+xs.length ≤ (pub 6).val) (before : (pub 6).val < G) :
    Represents out.privateMem top xs := by
  refine ⟨represented.1,fun i => ?_⟩
  have value : ((top+i.val : ℕ) : Word w).val = top+i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans represented.1)
  have lt : top+i.val < (pub 6).val := (Nat.add_lt_add_left i.isLt _).trans_le ends
  have sep : G ≤ (R).cacheBase := (R).hist_before
  exact (h.outside _ (fun eq => lt.ne (value.symm.trans (congrArg Fin.val eq)))
    (.inl (value.trans_lt (lt.trans before))) (.inl (value.trans_lt ((lt.trans before).trans_le sep)))).trans
    (represented.2 i)

include h in
theorem resident (before : (pub 6).val < G) (fit : G+12 ≤ 2^w) :
    ResidentGeometry (scratch (pub 6).val out.privateMem) (G : Word w) (st.reg (A.saved roleOffset))
      ((R).histBase : Word w) := by
  have bound (i : Fin 12) : G+i.val < 2^w := by have := i.isLt; omega
  have atField (i : Fin 12) :
      rawScratch (scratch (pub 6).val out.privateMem) ((G+i.val : ℕ) : Word w) =
        NativeFrame.fields degree pub (st.reg (A.saved header)) (st.reg (A.saved roleOffset)) m i := by
    have above : (pub 6).val ≤ ((G+i.val : ℕ) : Word w).val := by
      change _ ≤ (G+i.val)%_; rw [Nat.mod_eq_of_lt (bound i)]; omega
    rw [rawScratch,dite_eq_left above]
    exact h.fields i
  have addr (j : ℕ) (hj : j < 12) : ((G : Word w)+(j : Word w)).val = G+j := by
    rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt (bound ⟨j,hj⟩)]
  refine ⟨(pub 6).isLt,?_,?_,?_,?_,?_⟩
  · rw [show (10 : Word w) = ((10 : ℕ) : Word w) from rfl,addr 10 (by decide)]; omega
  · rw [show (11 : Word w) = ((11 : ℕ) : Word w) from rfl,addr 11 (by decide)]; omega
  · have v : (pub 6).val ≤ (((pub 6).val : ℕ) : Word w).val := by rw [Fin.cast_val_eq_self]
    rw [rawScratch,dite_eq_left v]; exact h.geometry.pointer
  · have word := atField (10 : Fin 12)
    change rawScratch (scratch (pub 6).val out.privateMem) ((G+10 : ℕ) : Word w) = st.reg (A.saved roleOffset) at word
    simpa only [Nat.cast_add,Nat.cast_ofNat] using word
  · have word := atField (11 : Fin 12)
    change rawScratch (scratch (pub 6).val out.privateMem) ((G+11 : ℕ) : Word w) = ((R).histBase : Word w) at word
    simpa only [Nat.cast_add,Nat.cast_ofNat] using word

include h in
theorem cacheScratch (before : (pub 6).val < G) (room : (R).cacheBase+38 ≤ 2^w) :
    Cached (R).cacheBase (rawScratch (scratch (pub 6).val out.privateMem)) vals := by
  intro j
  have hj : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
  have sep : G ≤ (R).cacheBase := (R).hist_before
  have above : (pub 6).val ≤ (((R).cacheBase+j.offset : ℕ) : Word w).val := by
    change _ ≤ ((R).cacheBase+j.offset)%_
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [rawScratch,dite_eq_left above]
  exact h.cache j

end PairSimulation.VertexGeometry.Ready

end VPVNP
end Computability
end OAI
