import OAI.Computability.BorderVNP.TeamTapeInputRouteSite

/-! # Dispatching one or two virtual sorter banks from pinned geometry bits

The routing program always prepares its primary bank. It reads the physical presence bit
in the literal and retains it for the subsequent verifier. Only a true bit stages the
second bank, using the following tagged virtual index and the next interior link segment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape TeamTapeSorting RAMSerialization

variable {d e w : ℕ}

/-- The remembered presence bit for the second virtual site. -/
abbrev secondFlag : Port := .work .size

/-- Optional secondary index field, with a physical presence bit at its head. -/
def secondId (v : Option (Word d)) : List Bool :=
  match v with
  | none => [false]
  | some u => true :: Evaluator.InputBank.fieldBits (wordBits u)

/-- The public metadata consumed by all router setup phases. -/
def metadataBits (n e w : ℕ) (v : Word d) (other : Option (Word d)) : List Bool :=
  sizeBits n d e w ++ (Evaluator.InputBank.fieldBits (wordBits v) ++ secondId other)

/-- Real-owner link bits. Absence of a second virtual block consumes no payload. -/
def ownerBits (a : Fields d e w) (v : Word d) (other : Option (Word d)) : List Bool :=
  rowBits a v ++ (other.elim [] (rowBits a))

private def flag (b : Bool) : FiniteRoutine Port := .ofRoutine (Routine.push secondFlag b)

private def optionalSite : FiniteRoutine Port := .ofRoutine (Routine.popCase metadata
  (Routine.halt false) (flag false).body ((flag true).followedBy (site true)).body)

/-- The fixed one/two-site dispatcher after reading the common suffix size. -/
def dispatch : FiniteRoutine Port := (site false).followedBy optionalSite

/-- The entire fixed loader from binary geometry and raw incident link streams. -/
def loader : FiniteRoutine Port := readSize.followedBy dispatch

/-- Record the optional-site bit and advance the public literal pointer past it. -/
def marked (s : Stacks Port) (b : Bool) (tail : List Bool) : Stacks Port :=
  Function.update (Function.update s metadata tail) secondFlag (b :: s secondFlag)

/-- Result after staging all real-owner virtual blocks. The saved presence bit chooses
exactly the same validation banks later. -/
def ownerOutput (a : Fields d e w) (v : Word d) (other : Option (Word d))
    (tail rest : List Bool) (s : Stacks Port) : Stacks Port :=
  match other with
  | none => marked (siteOutput false a v (false::tail) rest s) false tail
  | some u =>
    let first := siteOutput false a v (true :: (Evaluator.InputBank.fieldBits (wordBits u) ++ tail))
      (rowBits a u ++ rest) s
    siteOutput true a u tail rest (marked first true (Evaluator.InputBank.fieldBits (wordBits u) ++ tail))

/-- One virtual block's total setup time, including arbitrary bytes in the closed array. -/
def siteTime (d e w bytes : ℕ) := geometryTime d w (2^e) bytes + rowTime w (comparisonSize d e w)

/-- Number of virtual banks physically served by an owner. -/
def lanes (other : Option (Word d)) : ℕ := if other.isSome then 2 else 1

/-- The dispatcher reads the real public bit at the current metadata position. Primary
and secondary fields are consumed in order, with exactly two instructions for the branch
and the retained flag bit. -/
theorem dispatch_runs (a : Fields d e w) (v : Word d) (other : Option (Word d)) (s : Stacks Port)
    (tail rest : List Bool)
    (hi : s metadata = Evaluator.InputBank.fieldBits (wordBits v) ++ (secondId other ++ tail))
    (hs : s source = ownerBits a v other ++ rest) (hw : (s widthSource).length = w)
    (hH : (s bucket).length = 2^e) (hc : (s .suffixSize).length = comparisonSize d e w)
    (hm : s (.work .count) = []) (ht : s (.work .tmp) = []) (hz : ∀ b i, s (.post b i) = []) :
    dispatch.Runs (lanes other * siteTime d e w (s closedBlock).length + 2) s
      (ownerOutput a v other tail rest s) := by
  cases other with
  | none =>
    let f := siteOutput false a v (false :: tail) rest s
    have rf := site_runs false a v s (false :: tail) rest (by simpa [secondId] using hi)
      (by simpa [ownerBits] using hs) hw hH hc hm ht (hz false)
    have hmeta := (siteOutput_frame false a v (false::tail) rest s).1
    have put : (flag false).Runs 1 (Function.update f metadata tail) (marked f false tail) :=
      Routine.runs_push secondFlag false _
    have ro := Routine.runs_popCase_false metadata (Routine.halt false) (flag false).body
      ((flag true).followedBy (site true)).body hmeta put
    simpa only [dispatch, lanes, Option.isSome_none, Bool.false_eq_true, ite_false, one_mul, siteTime,
      ownerOutput, optionalSite, f] using rf.followedBy (show optionalSite.Runs 2 f (marked f false tail) from ro)
  | some u =>
    let publicTail := Evaluator.InputBank.fieldBits (wordBits u) ++ tail
    let f := siteOutput false a v (true :: publicTail) (rowBits a u ++ rest) s
    let mid := marked f true publicTail
    have rf := site_runs false a v s (true :: publicTail) (rowBits a u ++ rest)
      (by simpa [secondId,publicTail] using hi) (by simpa [ownerBits,List.append_assoc] using hs)
      hw hH hc hm ht (hz false)
    obtain ⟨hmeta,hsrc,hwidth,hbucket,hsize,hblock,hwork,hpost⟩ :=
      siteOutput_frame false a v (true :: publicTail) (rowBits a u ++ rest) s
    have put : (flag true).Runs 1 (Function.update f metadata publicTail) mid :=
      Routine.runs_push secondFlag true _
    have second := site_runs true a u mid tail rest (by simp [mid,marked,publicTail]) hsrc
      ((congrArg List.length hwidth).trans hw) ((congrArg List.length hbucket).trans hH)
      ((congrArg List.length hsize).trans hc) ((hwork .count).trans hm) ((hwork .tmp).trans ht)
      (fun i => (hpost i).trans (hz true i))
    have hb : mid closedBlock = s closedBlock := hblock
    rw [hb] at second
    have branch := Routine.runs_popCase_true metadata (Routine.halt false) (flag false).body
      ((flag true).followedBy (site true)).body hmeta (put.followedBy second)
    have together := rf.followedBy (show optionalSite.Runs _ f _ from branch)
    let D := siteTime d e w (s closedBlock).length
    change dispatch.Runs (2*D+2) s (siteOutput true a u tail rest mid)
    rw [show 2*D+2 = D+(1+D+1) by omega]
    exact together

/-- Bank with the consumed size field and its decoded tally. -/
def sized (s : Stacks Port) (L : ℕ) (tail : List Bool) : Stacks Port :=
  Function.update (Function.update s metadata tail) .suffixSize (List.replicate L true)

/-- Complete execution from the compact metadata and actual interior links, before the
sorter verifies the independently assigned records and messages. -/
theorem loader_runs (n : ℕ) (a : Fields d e w) (v : Word d) (other : Option (Word d)) (s : Stacks Port)
    (tail rest : List Bool) (fit : comparisonSize d e w ≤ n)
    (hi : s metadata = metadataBits n e w v other ++ tail) (hs : s source = ownerBits a v other ++ rest)
    (hw : (s widthSource).length = w) (hH : (s bucket).length = 2^e) (hc : s .suffixSize = [])
    (hb : s (.entry (.inl .bits)) = []) (hh : s (.entry (.inl .high)) = [])
    (htmp : s (.entry (.inl .scratch)) = []) (hm : s (.work .count) = [])
    (ht : s (.work .tmp) = []) (hz : ∀ b i, s (.post b i) = []) :
    let suffix := Evaluator.InputBank.fieldBits (wordBits v) ++ (secondId other ++ tail)
    let mid := sized s (comparisonSize d e w) suffix
    ∃ t ≤ 7*comparisonSize d e w + 9*Nat.clog 2 (n+1)+3 +
      (lanes other * siteTime d e w (s closedBlock).length + 2),
      loader.Runs t s (ownerOutput a v other tail rest mid) := by
  intro suffix mid
  obtain ⟨t,htime,parsed⟩ := readSize_runs n d e w fit s suffix
    (by simpa [suffix,metadataBits,List.append_assoc] using hi) hb hh htmp hc
  have raw := dispatch_runs a v other mid tail rest (by simp [mid,sized,suffix]) hs hw hH
    (by simp [mid,sized]) hm ht (fun b i => by simpa [mid,sized] using hz b i)
  exact ⟨_,Nat.add_le_add_right htime _,parsed.followedBy raw⟩

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
