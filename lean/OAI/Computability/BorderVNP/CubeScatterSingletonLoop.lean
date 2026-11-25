import OAI.Computability.BorderVNP.CubeScatterImage

/-! # Native singleton scatter over a runtime-sized interval

The loop issues one shared word copy or one binary local choice per physical
bit. Its output memory agrees with the per-position scatter model even though
the instruction table is independent of the length in the register.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Actual guard and ordinary instruction events of the counted native scatter. -/
def walkTrace : List Digit → Bank w → Memory w → List (TeamRAM.Event w)
  | [],_,_ => [tick w]
  | d::ds,r,m => tick w :: ((d.step r m).trace ++ walkTrace ds (d.step r m).bank (d.step r m).mem)

private theorem step_cursors (d : Digit) (r : Bank w) (m : Memory w) (one : r 59 = 1) :
    let t := (d.step r m).bank
    t 59 = 1 ∧ t 57 = r 57 ∧ t 38 = r 38 + 1 := by
  cases d with
  | privateBit b =>
    cases b <;> simp (config := {decide := true}) [Digit.step,Digit.mode,Mode.code,writeLocal,
      Code.block,effect,BinaryOp.eval,Function.update,one]
  | _ =>
    simp (config := {decide := true}) [Digit.step,Digit.mode,Mode.code,copyDigit,
      Code.block,effect,BinaryOp.eval,Function.update,one]

/-- At the physical cursor and end sentinel, all returning runs are precisely the
listed realizations of the fixed bit source, in the original wire order. -/
theorem walk_iff (mode : Mode) (len start : ℕ) (r : Bank w) (m : Memory w)
    (one : r 59 = 1) (cur : r 38 = word w start) (stop : r 57 = word w (start+len))
    (fits : start+len < 2^w) {es t mt} :
    Runs pub mac (.whileLt 38 57 mode.code) r m es t mt ↔
      ∃ ds, ds.map Digit.mode = List.replicate len mode ∧
        es = walkTrace ds r m ∧ t = (result ds r m).bank ∧ mt = (result ds r m).mem := by
  induction len generalizing start r m es t mt with
  | zero =>
    have ends : r 38 = r 57 := by simp [stop,cur]
    constructor
    · intro h
      cases h with
      | atom ha _ _ => cases ha
      | whileDone => exact ⟨[],rfl,rfl,rfl,rfl⟩
      | whileStep h _ _ => exact False.elim (h.ne ends)
    · rintro ⟨ds,hd,rfl,rfl,rfl⟩
      have eq : ds = [] := by simpa using hd
      subst ds
      exact .whileDone (by rw [ends]; exact lt_irrefl _)
  | succ len ih =>
    have guard : r 38 < r 57 := by
      change (r 38).val < (r 57).val
      rw [cur,stop,word_val _ _ (by omega),word_val _ _ fits]
      omega
    have succInput (d : Digit) :
        let next := (d.step r m).bank
        next 59 = 1 ∧ next 38 = word w (start+1) ∧ next 57 = word w (start+1+len) := by
      obtain ⟨o,e,v⟩ := step_cursors d r m one
      exact ⟨o,by rw [v,cur,word_add,word_one],by rw [e,stop]; congr 1; omega⟩
    constructor
    · intro h
      cases h with
      | atom ha _ _ => cases ha
      | whileDone hg => contradiction
      | whileStep _ first tail =>
        obtain ⟨d,hd,rfl,rfl,rfl⟩ := step_inv first
        obtain ⟨o,c,e⟩ := succInput d
        obtain ⟨ds,hds,rfl,rfl,rfl⟩ := (ih (start+1) _ _ o c e (by omega)).mp tail
        exact ⟨d::ds,by simp [hd,hds,List.replicate_succ],rfl,rfl,rfl⟩
    · rintro ⟨ds,hd,rfl,rfl,rfl⟩
      cases ds with
      | nil => simp [List.replicate_succ] at hd
      | cons d ds =>
        obtain ⟨hm,hds⟩ := List.cons.inj (show d.mode::ds.map Digit.mode = mode::List.replicate len mode by
          simpa [List.replicate_succ] using hd)
        obtain ⟨o,c,e⟩ := succInput d
        exact .whileStep guard (hm ▸ step_run _ _ d r m)
          ((ih (start+1) _ _ o c e (by omega)).mpr ⟨ds,hds,rfl,rfl,rfl⟩)

/-- The only choices are local singleton bits, each made at a positive-sign step. -/
theorem walk_cost (ds : List Digit) (r : Bank w) (m : Memory w) :
    let es := walkTrace ds r m
    TraceOK es (ds.flatMap Digit.choices) es.length ∧ traceCost es ≤ 5*ds.length+1 := by
  induction ds generalizing r m with
  | nil => simp [walkTrace,TraceOK,tick,traceCost,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra]
  | cons d ds ih =>
    obtain ⟨step,hs,hcost⟩ := d.trace_spec r m
    obtain ⟨rest,hr⟩ := ih (d.step r m).bank (d.step r m).mem
    refine ⟨by simpa [walkTrace] using (step.append rest).cons_tick,?_⟩
    change 1+traceCost ((d.step r m).trace++_) ≤ _
    simp only [traceCost,VPVNP.RAMBuckets.cost_append,List.length_cons]
    change 1+(traceCost (d.step r m).trace+traceCost (walkTrace ds _ _)) ≤ _
    omega

end Cube.Scatter

end BorderVNP
end Computability
end OAI
