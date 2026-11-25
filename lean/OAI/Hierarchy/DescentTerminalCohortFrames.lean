import OAI.Hierarchy.DescentTerminalCohortRun

namespace OAI
/-! # The stable cohort census preserves memory on both sides of its allocated tables -/
namespace Hierarchy.DescentTerminalCohortArena
open DescentCensusRAM DescentTerminalFrozenRoster DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

private theorem add_high {w n B : ℕ} (S : Banks w n B) (key val : Expr) (t : Fin n→Fin B)
    (wt : Fin n→ℕ) (m : Memory w) {a : ℕ} (high : S.bins+B ≤ a) :
    afterAdd S key val t wt m a=m a := by
  let dest (i : Fin n) := S.bins+(t i).val
  have tape := S.beforeBins
  have keep (d : ℕ) (hd : d<2) (v : Expr) (x : Fin n→ℕ) (mem : Memory w) :
      issued S d v x mem a=mem a :=
    issued_away S d v x mem a (.inr (by omega)) (fun i=>by
      have := i.isLt
      unfold atSlot
      omega)
  change ProtocolRAMWeightedScatter.image dest wt _ n a=m a
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (fun i=>by
    have := (t i).isLt
    dsimp [dest]
    omega)]
  exact (keep 1 (by decide) _ _ _).trans (keep 0 (by decide) _ _ _)

/-- The clipped native owner lookup always chooses a bin in the actual allocated census. -/
private theorem roster_frame {w n H : ℕ} (S : Banks w n (H+1)) (L : Shelf) (m : Memory w)
    (kf : (tag L S.bins H).Fits w S.first) (vf : (value L).Fits w S.first) :
    ∃ out, (DescentTerminalFrozenRoster.program S L).Exec m out
      (tallyCost S (tag L S.bins H) (value L)) ∧
      ∀a, a<S.first ∨ S.bins+(H+1)≤a → out a=m a := by
  let t (i : Fin n) : Fin (H+1) := ⟨min ((owner L).eval m (i.val:Word w)).val H,by omega⟩
  let wt (i : Fin n) := ((value L).eval m (i.val:Word w)).val
  let clear := ProtocolRAM.image S.bins (H+1) (.lit 0) m
  have hi : H<2^w := by have := S.finish;omega
  have keys (i : Fin n) : (tag L S.bins H).eval m (i.val:Word w)=((S.bins+(t i).val:ℕ):Word w) := by
    let x := (owner L).eval m (i.val:Word w)
    have tested : DescriptorExpr.Comparison.lt.test x (H:Word w)=true ↔ x.val<H := by
      simp only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt hi]
    change (S.bins:Word w)+(if DescriptorExpr.Comparison.lt.test x (H:Word w) then x else (H:Word w)) =
      ((S.bins+min x.val H:ℕ):Word w)
    by_cases small : x.val<H
    · simp only [ite_eq_left (tested.mpr small),min_eq_left small.le,Nat.cast_add,Fin.cast_val_eq_self]
    · simp only [ite_eq_right (mt tested.mp small),min_eq_right (le_of_not_gt small),Nat.cast_add]
  have ordering : S.first≤S.bins := by
    have := S.scratch;have := S.beforeTape;have := S.beforeBins;omega
  have keep (a : ℕ) (lo : a<S.first) : clear a=m a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (lo.trans_le ordering))
  have init : (scan w S.bins (H+1) (.lit 0)).Exec m clear (4+(H+1)*6) :=
    scan_exec S.bins (H+1) (.lit 0) m trivial S.finish
  let key:=tag L S.bins H
  let value_:=value L
  have addRun : (add S key value_).Exec clear (afterAdd S key value_ t wt clear) (addCost S key value_) :=
    add_exec S key value_ t wt clear kf vf
      (fun i=>(eval_below key _ m clear kf keep).trans (keys i))
      (fun i=>by rw [eval_below value_ _ m clear vf keep];exact (Fin.cast_val_eq_self _).symm)
  refine ⟨afterAdd S key value_ t wt clear,?_,?_⟩
  · intro P R K machine pc reg pub exit code data cfg raw entry eqn
    exact Procedure.Exec.then init addRun machine pc reg pub exit code data cfg raw entry eqn
  · intro a away
    rcases away with lo|high
    · exact (add_frame S key value_ t wt clear a lo).trans (keep a lo)
    · exact (add_high S key value_ t wt clear high).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr high))

/-- Even a malformed incoming word passes through the guarded sort and the clipped
census. All of their writes stay inside the same static allocation. -/
theorem any_frame {w : ℕ} (base f k n H : ℕ) (room : stop base f k n H<2^w) (source : Bank)
    (m : Memory w) (alive : 0<H) (src : source.Fits w base) :
    ∃o, (machine base f k n H room source).Exec m o (ticks base f k n H room source) ∧
      CheapCode (machine base f k n H room source) ∧
      ∀a, a<base ∨ stop base f k n H≤a → o a=m a := by
  let O:=order base f k n H
  let S:=shelf base f k n H room
  let L:=roster base f k n H
  let first:=ROM.mounted base f k m
  let second:=sorted source O H n alive first
  let third:=after O n H second
  obtain ⟨sr,range,rom,_,safe,paid⟩:=layout base f k n H room source src
  have mounted:=ROM.run base f k m rom
  have sorter:=DescentTerminalPacketSlotRAM.run source O first alive sr range
  obtain ⟨o,write,hist⟩:=roster_frame S L third safe paid
  let sortProgram := DescentTerminalPacketSlotRAM.program source O w n H
  refine ⟨o,Procedure.Exec.then (Procedure.Exec.then mounted.1 sorter.1) write,
    @cheap_seq w ((ROM.setup base f k w).seq sortProgram) (DescentTerminalFrozenRoster.program S L)
      (@cheap_seq w (ROM.setup base f k w) sortProgram mounted.2.1 sorter.2)
      (@tally_cheap w n (H+1) S (tag L S.bins H) (value L)),?_⟩
  intro a away
  have firstBase : O.src=base+ROM.size f k := rfl
  have hs := sr.fits.src_safe
  have hc := sr.fits.count_safe
  have hp := sr.fits.prefix_safe
  change O.src+n≤O.counts at hs
  change O.counts+H≤O.starts at hc
  change O.starts+H+1≤O.sorted at hp
  have ns := Nat.le_pow_clog (by decide : 1<2) n
  have sortIndex : O.sorted+n≤out O n H :=
    (Nat.add_le_add_left ns _).trans (Nat.le_add_right (O.sorted+(bank 0 n).size) _)
  have indexTally : out O n H+n≤S.first := Nat.add_le_add_left ns _
  have binEnd : S.bins+(H+1)=stop base f k n H := by
    change tallyBase base f k n H+4*n+(H+1)=tallyBase base f k n H+4*n+H+1
    omega
  have within : S.first≤S.bins := by
    have := S.scratch;have := S.beforeTape;have := S.beforeBins;omega
  have sortedFrame : second a=first a :=
    (ProtocolRAMEndpointSort.frame O sr.fits (observed (n:=n) source H first alive)
      (keys source O H n first) a (by rcases away with low|high <;> omega)
      (by rcases away with low|high <;> omega) (by rcases away with low|high <;> omega)).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by rcases away with low|high <;> omega))
  exact (hist a (by rcases away with low|high <;> omega)).trans
    ((retained O n H second a (by rcases away with low|high <;> omega)).trans
      (sortedFrame.trans (mounted.2.2.2 a (by rcases away with low|high <;> omega))))

end
end Hierarchy.DescentTerminalCohortArena

end OAI
