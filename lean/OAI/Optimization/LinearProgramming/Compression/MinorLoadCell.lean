import OAI.Optimization.LinearProgramming.Compression.MinorLoadData
import OAI.Optimization.LinearProgramming.Compression.UniformIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

variable {K : Type}

abbrev Good (P : K → Prop) (s : Memory K) := ∀ r, P (s.data r)

private theorem good_put {P : K → Prop} {s : Memory K} (h : Good P s) (r : ℕ) {x : K}
    (hx : P x) : Good P (s.putData r x) := by
  intro p
  by_cases he : p = r
  · subst p; simpa [Memory.putData] using hx
  · simpa [Memory.putData, Function.update_of_ne he] using h p

structure Outer (P : K → Prop) (v : Layout K) (src : Memory K) (i : ℕ) (s : Memory K) : Prop where
  frame : Frame v src s
  copied : Copied v s (i*v.k)
  cnt : s.index 6 = i
  ptr : s.index 8 = v.rowArray+i
  dst : s.index 15 = v.dst+i*v.k
  safe : Good P s

structure Inner (P : K → Prop) (v : Layout K) (src : Memory K) (i : Fin v.k) (j : ℕ)
    (s : Memory K) : Prop where
  frame : Frame v src s
  copied : Copied v s (i.val*v.k+j)
  rcnt : s.index 6 = i.val
  ccnt : s.index 7 = j
  rptr : s.index 8 = v.rowArray+i.val
  cptr : s.index 9 = v.colArray+j
  row : s.index 10 = (v.row i).val
  dst : s.index 15 = v.dst+(i.val*v.k+j)
  safe : Good P s

/-- After calculating the source address, copy one scalar and advance the cursors. -/
def cellTail : Block :=
  .seq (.op (.load 0 12)) (.seq (.op (.store 15 0))
    (.seq (.op (.incr 15 15)) (.seq (.op (.incr 9 9)) (.op (.incr 7 7)))))

def cellBody : Block :=
  .seq (.op (.addrLoad 11 9)) (.seq (cellAddress 12 13 14 0 1 10 11) cellTail)

def cellCost (v : Layout K) (i j : Fin v.k) : ℕ :=
  (v.row i).val*(4*v.n+5)+4*(v.col j).val+11

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem cell_eval {P : K → Prop} {v : Layout K} {src s : Memory K} (hinput : Input v src)
    (i j : Fin v.k) (h : Inner P v src i j.val s) :
    ∃ t, Block.Eval (Good P) cellBody s (cellCost v i j) t ∧ Inner P v src i (j.val+1) t := by
  let a := s.putIndex 11 (s.index (s.index 9))
  have first : Block.Eval (Good P) (.op (.addrLoad 11 9)) s 1 a :=
    Block.Eval.op_addrLoad _ _ _ h.safe h.safe
  have ha : Frame v src a := h.frame.putIndex (by decide) (by decide) _
  have inp := hinput.of_frame h.frame
  have ca : a.index 11 = (v.col j).val := by simp [a, Memory.putIndex, h.cptr, inp.cols]
  have ra : a.index 10 = (v.row i).val := by simp [a, Memory.putIndex, h.row]
  have hsrc := (hinput.of_frame ha).src
  have hw := (hinput.of_frame ha).width
  obtain ⟨z, haddr, hdata, hkeep, hresult⟩ := cellAddress_spec (fun f => ∀ p, P (f p)) a h.safe
    12 13 14 0 1 10 11 (by norm_num [CellScratchOK])
  rw [hsrc, ra, hw, ca] at hresult
  have hz : Frame v src z := ha.cellAddress hdata hkeep
  have keep (p : ℕ) (hp : p < 11 ∨ p = 15) : z.index p = s.index p :=
    (hkeep p (by omega) (by omega) (by omega)).trans
      (by simp [a, Memory.putIndex, Function.update_of_ne (show p ≠ 11 by omega)])
  let x := v.matrix (v.row i) (v.col j)
  have hload : z.data (z.index 12) = x := by rw [hresult]; exact (hinput.of_frame hz).source _ _
  let u := z.putData 0 x
  have hs : Good P z := haddr.safe_end
  have hx : P x := hload ▸ hs (z.index 12)
  have hu : Good P u := good_put hs 0 hx
  have load : Block.Eval (Good P) (.op (.load 0 12)) z 1 u := by
    simpa only [hload] using Block.Eval.op_load (safe := Good P) z 0 12 hs (hload.symm ▸ hu)
  let w := u.putData (v.dst+(i.val*v.k+j.val)) x
  have hs' : Good P w := good_put hu _ hx
  have hd : u.index 15 = v.dst+(i.val*v.k+j.val) := (keep _ (by decide)).trans h.dst
  have htmp : u.data 0 = x := by simp [u, Memory.putData]
  have save : Block.Eval (Good P) (.op (.store 15 0)) u 1 w := by
    simpa only [hd, htmp] using Block.Eval.op_store (safe := Good P) u 15 0 hu
      (by simpa only [hd, htmp] using hs')
  let w₁ := w.putIndex 15 (w.index 15+1)
  let w₂ := w₁.putIndex 9 (w₁.index 9+1)
  let t := w₂.putIndex 7 (w₂.index 7+1)
  have tail : Block.Eval (Good P) cellTail z 5 t := load.seq (save.seq
    ((Block.Eval.op_incr w 15 15 hs' hs').seq
    ((Block.Eval.op_incr w₁ 9 9 hs' hs').seq (Block.Eval.op_incr w₂ 7 7 hs' hs'))))
  have whole := first.seq (haddr.seq tail)
  rw [ra, hw, ca] at whole
  have ht : Block.Eval (Good P) cellBody s (cellCost v i j) t := by
    unfold cellBody cellCost
    convert whole using 1; omega
  have hwframe : Frame v src w := (hz.putTemp x).putOutput (flat_lt i.isLt j.isLt) x
  have hc : Copied v z (i.val*v.k+j.val) := h.copied.of_data_eq hdata
  have hcopied : Copied v w (i.val*v.k+j.val+1) := (hc.putTemp x).putNext i j
  have p6 := (keep 6 (by decide)).trans h.rcnt
  have p7 := (keep 7 (by decide)).trans h.ccnt
  have p8 := (keep 8 (by decide)).trans h.rptr
  have p9 := (keep 9 (by decide)).trans h.cptr
  have p10 := (keep 10 (by decide)).trans h.row
  have p15 := (keep 15 (by decide)).trans h.dst
  refine ⟨t, ht, ⟨((hwframe.putIndex (by decide) (by decide) _).putIndex (by decide) (by decide) _).putIndex
    (by decide) (by decide) _, hcopied, ?_, ?_, ?_, ?_, ?_, ?_, hs'⟩⟩ <;>
    simp [t,w₂,w₁,w,u,Memory.putIndex,Memory.putData,p6,p7,p8,p9,p10,p15,Nat.add_assoc]

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
