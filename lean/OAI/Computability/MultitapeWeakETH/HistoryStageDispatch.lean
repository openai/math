import OAI.Computability.MultitapeWeakETH.HistoryLayout
import OAI.Computability.VPVNP.PairVertexLevelSchedule
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Selecting a fixed local kernel by its chronological pass ordinal -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression PairSimulation LocalHistory CompressorRecords

private def chooseAt {A Y : Type} (fs : List (A → Y)) (fallback : A → Y) (q : Tally × A) :=
  (fs[q.1.length]?.getD fallback) q.2

private theorem chooseAt_poly {A Y : Type} [Codec A] [Codec Y] (fs : List (A → Y)) (fallback : A → Y)
    (hf : ∀ f ∈ fs, Poly f) (hb : Poly fallback) : Poly (chooseAt fs fallback) := by
  induction fs with
  | nil => exact Easy.snd.poly.compose hb
  | cons f fs ih =>
    have empty : Poly (fun t : Tally => t.isEmpty) := by
      convert (Easy.listCase (X:=Unit) true (Easy.const false)).poly using 1
      funext t; cases t <;> rfl
    have tl : Poly (fun t : Tally => t.tail) := by
      convert (Easy.listCase (X:=Unit) [] Easy.snd).poly using 1
      funext t; cases t <;> rfl
    have pick := Poly.choose (Easy.fst.poly.compose empty) (Easy.snd.poly.compose (hf _ List.mem_cons_self))
      (((Easy.fst.poly.compose tl).pair Easy.snd.poly).compose (ih (fun g hg => hf g (List.mem_cons_of_mem _ hg))))
    convert pick using 1
    funext ⟨xs,a⟩
    cases xs <;> rfl

/-- Each full block runs its shrinking stages in order and then one refresh. -/
def dispatch {A Y : Type} {stages : ℕ} (shrinking : Fin stages → A → Y) (refresh : A → Y) (q : Tally × A) :=
  chooseAt (List.ofFn shrinking) refresh ((Staff.quot (q.1,tally (stages+1))).2,q.2)

theorem dispatch_poly {A Y : Type} [Codec A] [Codec Y] {stages : ℕ}
    {shrinking : Fin stages → A → Y} {refresh : A → Y} (hs : ∀ i, Poly (shrinking i)) (hr : Poly refresh) :
    Poly (dispatch shrinking refresh) := by
  have all (f) (mem : f ∈ List.ofFn shrinking) : Poly f := by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem; exact hs i
  exact ((((Easy.fst.poly.pair (Code.Poly.const _)).compose Staff.stable_q.sndCompose).pair Easy.snd.poly)).compose
    (chooseAt_poly _ _ all hr)

theorem dispatch_eq {A Y : Type} {stages : ℕ} (shrinking : Fin stages → A → Y) (refresh : A → Y) (j : ℕ) (x : A) :
    dispatch shrinking refresh (tally j,x) =
      if h : j%(stages+1) < stages then shrinking ⟨_,h⟩ x else refresh x := by
  unfold dispatch chooseAt
  rw [Staff.quot_r]
  simp only [Staff.box,tally_length]
  split
  next h =>
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    rfl
  next h =>
    rw [List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt h)]
    rfl

/-- The clock selects the actual origin of every pass on every chosen descriptor
history. Its program does not inspect the mathematical choice path. -/
theorem dispatch_origin {A Y k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ) (fit : T*S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (path : (B.execute f hf T fit X).Choices)
    (shrinking : Fin S.steps → A → Y) (refresh : A → Y) (j : Fin (executeLevels B f hf T fit X path).length) (x : A) :
    let index := (executeLevels B f hf T fit X path)[j.val].origin.ordinal
    dispatch shrinking refresh (tally j.val,x) = if h : index < S.steps then shrinking ⟨index,h⟩ x else refresh x := by
  intro index
  let choose (a : ℕ) := if h : a < S.steps then shrinking ⟨a,h⟩ x else refresh x
  have stage : index = j.val % (S.steps + 1) := VertexLevel.selected_pass_ordinal B f hf T fit X path j
  exact (dispatch_eq shrinking refresh j.val x).trans (congrArg choose stage.symm)

end OAI.Computability.MultitapeWeakETH.NativeGrid
