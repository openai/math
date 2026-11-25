import OAI.ThreeFlat.Diagonal.HistoryRegister
import OAI.ThreeFlat.Diagonal.RotatedChunkGuards

namespace OAI
/-! # Chronological composition through canonical physical register states -/

namespace ThreeFlat.Diagonal.GuardedTransfer

open scoped BigOperators Classical
noncomputable section
variable {F U X Y Z H : Type*} [CommSemiring F] [Fintype U] [Fintype X] [Fintype Y] [Fintype Z]

/-- Read an actual physical row at the register encoding of a logical state. -/
def rows (e : X → U) : Matrix X U F := fun i u => if e i = u then 1 else 0

omit [Fintype X] [Fintype Y] in
theorem rows_mul (e : X → U) (M : Matrix U Y F) (x : X) (y : Y) :
    ((rows (F:=F) e * M : Matrix X Y F)) x y = M (e x) y := by
  simp [Matrix.mul_apply,rows,ite_mul]

omit [Fintype X] in
theorem rows_transpose (e : X ↪ U) : rows (F:=F) e * (rows (F:=F) e).transpose = (1 : Matrix X X F) := by
  ext i j
  rw [rows_mul]
  simp only [Matrix.transpose_apply,rows,Matrix.one_apply, e.injective.eq_iff]
  by_cases h : i=j <;> simp [h,eq_comm]

omit [Fintype X] [Fintype Y] in
theorem read_endpoints (e : X → U) (M : Matrix U U F) (f : Y → U) :
    rows e * M * (rows f).transpose = M.submatrix e f := by
  ext i j
  simp [Matrix.mul_apply,rows,Matrix.transpose_apply,ite_mul,mul_ite,Matrix.submatrix_apply]

/-- Starting at an encoded boundary, each nonzero output is supported on the new encodings.
Intermediate branch registers may have different alphabets at successive phase boundaries. -/
def Tracks (e : X → U) (f : Y → U) (M : Matrix U U F) (A : Matrix X Y F) : Prop :=
  rows e * M = A * rows f

omit [Fintype X] in
theorem tracks_of_entries (e : X → U) (f : Y → U) (M : Matrix U U F) (A : Matrix X Y F)
    (entries : ∀ x u, M (e x) u = ∑ j : Y, if f j=u then A x j else 0) : Tracks e f M A := by
  ext x u
  rw [rows_mul,entries,Matrix.mul_apply]
  simp [rows,mul_ite]

omit [Fintype X] in
theorem Tracks.comp {e : X → U} {f : Y → U} {g : Z → U} {M N : Matrix U U F} {A : Matrix X Y F} {B : Matrix Y Z F}
    (a : Tracks e f M A) (b : Tracks f g N B) : Tracks e g (M*N) (A*B) := by
  unfold Tracks at *
  rw [← Matrix.mul_assoc,a,Matrix.mul_assoc,b,← Matrix.mul_assoc]

theorem tracks_list {I : Type*} (e : X → U) (is : List I) (M : I → Matrix U U F) (A : I → Matrix X X F)
    (step : ∀ i ∈ is, Tracks e e (M i) (A i)) : Tracks e e (is.map M).prod (is.map A).prod := by
  induction is with
  | nil => simp [Tracks]
  | cons i is ih =>
    rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons]
    exact (step i (by simp)).comp (ih (fun j hj => step j (by simp [hj])))

omit [Fintype X] in
theorem Tracks.restrict {e : X → U} {f : Y ↪ U} {M : Matrix U U F} {A : Matrix X Y F}
    (a : Tracks e f M A) : M.submatrix e f = A := by
  rw [← read_endpoints,a,Matrix.mul_assoc,rows_transpose,Matrix.mul_one]

/-- An opening, any number of physical groups, and the closing transition. The identity marker
and every admitted shared terminal record are each summed exactly once. -/
theorem switched_run [Fintype H] [DecidableEq H] [DecidableEq X] {I : Type*} (e : X ↪ U) (live : X × Option H → U)
    (openM closeM : Matrix U U F) (is : List I) (group : I → Matrix U U F) (A : I → H → Matrix X X F)
    (first : Tracks e live openM (openHistory (H := Option H)))
    (each : ∀ i ∈ is, Tracks live live (group i) (Matrix.blockDiagonal (fun h : Option H => h.elim 1 (A i))))
    (last : Tracks live e closeM (openHistory (H := Option H)).transpose) :
    (openM*(is.map group).prod*closeM).submatrix e e = 1 + ∑ h, (is.map (fun i => A i h)).prod := by
  have run := (first.comp (tracks_list live is group _ each)).comp last
  rw [run.restrict]
  convert! switched_history_evaluation is A using 4; congr! 6

/-- All phases of a group share the same proposed old and new pair strings. The clear sums over
exactly the pair values admitted by the scan. -/
theorem group_run [Fintype H] [DecidableEq H] [DecidableEq X] {I : Type*} (outer : X ↪ U) (live : X × H → U)
    (propose clear : Matrix U U F) (is : List I) (phase : I → Matrix U U F) (A : I → H → Matrix X X F)
    (first : Tracks outer live propose (openHistory (H := H)))
    (each : ∀ i ∈ is, Tracks live live (phase i) (Matrix.blockDiagonal (A i)))
    (last : Tracks live outer clear (openHistory (H := H)).transpose) :
    Tracks outer outer (propose*(is.map phase).prod*clear) (∑ h, (is.map (fun i => A i h)).prod) := by
  have run := (first.comp (tracks_list live is phase _ each)).comp last
  have endEq := run_persistent_history is A
  convert! run using 1
  symm
  convert! endEq using 4; congr! 6

end
end ThreeFlat.Diagonal.GuardedTransfer

end OAI
