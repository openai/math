import OAI.ThreeFlat.Diagonal.TraceEndpointSlice
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Fixed native restriction of a leaf record to its independent endpoint inputs -/

namespace ThreeFlat.RAM.TraceSuffixProgram
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSuffix
open scoped Fin.CommRing
variable {W K : ℕ}

/-- Inputs are original field word, field index, stage, global start, old
local pin count and retained local pin count. The native public-source
reader is sampled once at a global tape position. -/
def glue (oracle : Term W K 1) : Term W K 6 :=
  let x := Term.result 0
  let field := Term.result 1
  let stage := Term.result 2
  let start := Term.result 3
  let old := Term.result 4
  let kept := Term.result 5
  let two := Term.literal 2
  let pos := Term.binary .add start (Term.binary .sub x two)
  let read := oracle.instantiate (fun _ => pos)
  let adjusted := Term.binary .sub x (Term.binary .sub old kept)
  let sources := Term.select .lt x (Term.binary .add two kept) x
    (Term.select .lt x (Term.binary .add two old) read adjusted)
  Term.select .eq stage (.literal 0) (Term.select .lt field (.literal 3) sources x) x

private def aperture {n : ℕ} (size start extent : Term W K n) :=
  let past := Term.binary .add start extent
  Term.select .lt size start (.literal 0)
    (Term.select .lt size past (Term.binary .sub size start) extent)

/-- Public slots contain the old header length, twice the number of
endpoint coordinates, and the number of pins per lane before clipping. -/
def program (raw : Term W K 4) (oracle : Term W K 1) (header «prefix» span : Fin K) : Term W K 4 :=
  let extent := Term.parameter span
  let start := Term.binary .mul (Term.result 2) extent
  (glue oracle).instantiate ![raw,.result 1,.result 3,start,
    aperture (.parameter header) start extent,aperture (.parameter «prefix») start extent]

theorem program_size (raw : Term W K 4) (oracle : Term W K 1) (header «prefix» span : Fin K) :
    (program raw oracle header «prefix» span).binds≤raw.binds+oracle.binds+100 := by
  simp [program,glue,aperture,Term.binds_instantiate,Fin.sum_univ_succ,Term.select,Term.binary,
    Term.literal,Term.parameter,Term.binds,Finset.univ_unique]; omega

private theorem test (op : Comparison) {x y : ℕ} (hx : x<2^W) (hy : y<2^W) :
    op.test (x : Word W) (y : Word W)=natTest op x y := test_cast op _ _ hx hy

private theorem minus {x y : ℕ} (h : y≤x) : (x : Word W)-(y : Word W)=(x-y : ℕ) := by
  rw [Nat.cast_sub h]

private theorem aperture_at {n : ℕ} (size start extent : Term W K n)
    (params : Fin K→Word W) (m : Memory W) (vs : Fin n→Word W) {a z l : ℕ}
    (s : size.eval params m vs=(a : Word W)) (t : start.eval params m vs=(z : Word W))
    (e : extent.eval params m vs=(l : Word W)) (sa : a<2^W) (sz : z+l<2^W) :
    (aperture size start extent).eval params m vs=(min l (a-z) : ℕ) := by
  have rz : z<2^W := by omega
  simp only [aperture,Term.eval_binary,Term.eval_select,Term.eval_literal,s,t,e]
  change (if Comparison.lt.test (a : Word W) (z : Word W) then 0 else
    if Comparison.lt.test (a : Word W) ((z : Word W)+l) then (a : Word W)-z else l) = _
  rw [←Nat.cast_add,test .lt sa rz,test .lt sa sz]
  by_cases first : a<z
  · simp [natTest,first,Nat.sub_eq_zero_of_le first.le]
  · by_cases last : a<z+l
    · simp [natTest,first,last,minus (show z≤a by omega),Nat.min_eq_right (by omega : a-z≤l)]
    · simp [natTest,first,last,Nat.min_eq_left (by omega : l≤a-z)]

theorem glue_at (oracle : Term W K 1) (params : Fin K→Word W) (m : Memory W)
    (start old kept x j stage : ℕ) (pub : ℕ→Bool) (clip : kept≤old)
    (input : x<2^W) (sj : j<2^W) (st : stage<2^W) (hi : 3<2^W)
    (ap : 2+old<2^W) (oracleAt : 2+kept≤x → x<2+old → stage=0 → j<3 →
      oracle.eval params m (fun _ => (start+(x-2) : ℕ))=(pub (start+(x-2))).toNat) :
    (glue oracle).eval params m ![x,j,stage,start,old,kept]=
      ((if stage=0 then field old kept start pub j x else x : ℕ) : Word W) := by
  have hz : 0<2^W := Nat.two_pow_pos _
  have kk : 2+kept<2^W := by omega
  simp only [glue,Term.eval_select,Term.eval_instantiate,Term.eval_binary,Term.eval_literal,Term.eval]
  change (if Comparison.eq.test (stage : Word W) ((0 : ℕ) : Word W) then
    if Comparison.lt.test (j : Word W) ((3 : ℕ) : Word W) then
      if Comparison.lt.test (x : Word W) (2+(kept : Word W)) then (x : Word W) else
        if Comparison.lt.test (x : Word W) (2+(old : Word W)) then
          oracle.eval params m (fun _ => (start : Word W)+((x : Word W)-((2 : ℕ) : Word W)))
        else (x : Word W)-((old : Word W)-(kept : Word W))
      else (x : Word W) else (x : Word W)) = _
  rw [show (2+(kept : Word W))=((2+kept : ℕ):Word W) by simp,
    show (2+(old : Word W))=((2+old : ℕ):Word W) by simp,
    test .eq st hz,test .lt sj hi,test .lt input kk,test .lt input ap]
  by_cases h0 : stage=0 <;> by_cases h3 : j<3 <;> by_cases live : x<2+kept <;> by_cases source : x<2+old <;>
    simp only [natTest,field,address,h0,h3,live,source,decide_true,decide_false,ite_true,ite_false,
      Bool.false_eq_true] <;> first
    | rfl
    | rw [minus (show 2≤x by omega),←Nat.cast_add,oracleAt (by omega) source h0 h3]
    | rw [minus clip,minus (show old-kept≤x by omega)]

set_option maxHeartbeats 700000 in
theorem program_at (raw : Term W K 4) (oracle : Term W K 1) (header «prefix» span : Fin K)
    (params : Fin K→Word W) (m : Memory W) (vs : Fin 4→Word W)
    (S T step start x : ℕ) (pub : ℕ→Bool)
    (stepAt : params span=(step : Word W)) (headerAt : params header=(S : Word W))
    (prefixAt : params «prefix»=(2*T : ℕ)) (posAt : (vs 2).val*step=start)
    (rawAt : raw.eval params m vs=(x : Word W)) (input : x<2^W)
    (fit : 2*T≤S) (hs : 2+S<2^W) (site : start+step<2^W) (hi : 3<2^W)
    (oracleAt : 2+min step (2*T-start)≤x → x<2+min step (S-start) → (vs 3).val=0 → (vs 1).val<3 →
      oracle.eval params m (fun _ => (start+(x-2) : ℕ))=(pub (start+(x-2))).toNat) :
    (program raw oracle header «prefix» span).eval params m vs=
      ((if (vs 3).val=0 then field (min step (S-start)) (min step (2*T-start)) start pub (vs 1).val x else x : ℕ) : Word W) := by
  let width := (Term.parameter span : Term W K 4)
  let pos := (Term.binary .mul (.result 2) width)
  have widthAt : width.eval params m vs=(step : Word W) := stepAt
  have pAt : pos.eval params m vs=(start : Word W) := by
    simp only [pos,Term.eval_binary,Term.eval,widthAt]
    change (vs 2)*(step : Word W)=_
    rw [←posAt,Nat.cast_mul]; simp
  have values :
      (fun t => (![raw,Term.result 1,Term.result 3,pos,aperture (.parameter header) pos width,
        aperture (.parameter «prefix») pos width] t).eval params m vs) =
        ![(x : Word W),vs 1,vs 3,(start : Word W),(min step (S-start) : ℕ),(min step (2*T-start) : ℕ)] := by
    funext i
    fin_cases i
    · exact rawAt
    · rfl
    · rfl
    · exact pAt
    · exact aperture_at (.parameter header) pos width params m vs headerAt pAt widthAt (by omega) site
    · exact aperture_at (.parameter «prefix») pos width params m vs prefixAt pAt widthAt (by omega) site
  rw [program,Term.eval_instantiate]
  change (glue oracle).eval params m _=_
  rw [values]
  simpa only [Fin.cast_val_eq_self] using glue_at oracle params m start (min step (S-start)) (min step (2*T-start))
    x (vs 1).val (vs 3).val pub (by omega) input
    (vs 1).isLt (vs 3).isLt hi (by have := Nat.min_le_right step (S-start); omega) oracleAt


end ThreeFlat.RAM.TraceSuffixProgram

end OAI
