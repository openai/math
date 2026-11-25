import OAI.Computability.NearSquareRoot.InterchangeROMBankCarve
import OAI.Computability.NearSquareRoot.InterchangeROMBankCompose
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAligned

/-! # Opening a bank of flat center rows

Each numeric selector preserves the three shared rulers during its scan, then
carves the selected row. The first carved row supplies the prefix scaffold used
to discard padding during the inverse bank permutation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication Code Strip
open CommonRegisters GeneratorSyntax LoomRegisters Space InterchangeROMBankCarve

open private scaffold from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomAligned

private noncomputable def openCell (i : ℕ) : Cmd :=
  (InterchangeROM.underHeader (cellCommand i)).join carveCommand

/-- One compiled bank opening, with the bank width in the file and all three
row dimensions supplied on the physical input tape. -/
noncomputable def openBank (W : ℕ) : Cmd :=
  (seriesCommand openCell (List.range W)).join (scaffold 0)

theorem effective_openBank : Effective ltr openBank := by
  apply Effective.join _ (effective_const _ _)
  apply InterchangeROM.effective_series
  · exact (InterchangeROM.effective_underHeader (InterchangeROM.effective_cell Computable.snd)).join
      (effective_const _ _)
  · exact Primrec.list_range.to_comp

theorem openBank_within : ∃ R, 4 ≤ R ∧ ∀ W, Within R (openBank W) := by
  obtain ⟨R,hR,hc⟩ := ((Filter.eventually_ge_atTop 4).and
    (RegisterSelect.within_eventually carveCommand)).exists
  refine ⟨R,hR,fun W => ⟨series_within (by omega) _ _ (fun i =>
    ⟨InterchangeROM.underHeader_within (by omega) (RegisterSelect.within_mono (by omega : 3 ≤ R)
      _ (cell_within i)),hc⟩), RegisterSelect.within_mono hR _ (scaffold_within 0)⟩⟩

private theorem cell_count {A : Type} (s : Series A) (f : A → Tree) (a : A) :
    (f a).count ≤ (stripe s f).count := by
  rw [stripe_simple]
  exact count_le_forest f (s.complete a)

private theorem selectRun {W : ℕ} (header : Tree) (v : Fin W → Tree) (i : Fin W) :
    Run (InterchangeROM.underHeader (cellCommand i.val)) 105 106
      (.fork header (stripe (Series.natural W) v)) (.fork header (v i)) := by
  let b := stripe (Series.natural W) v
  intro env r base hb
  have read (d : Deck) : Fits env (cellCommand i.val) (pile 0 b d) (pile 0 (v i) d) (90*b.count) := by
    have e := cell_fits v (List.finRange W) _ i (List.getElem?_idxOf (List.mem_finRange i)) env d
    rw [List.idxOf_finRange] at e
    change Fits _ _ (pile 0 (stripe (Series.natural W) v) _) _ (90 * (stripe (Series.natural W) v).count)
    simpa only [stripe_simple,Series.natural,Series.fixed] using e
  have run := InterchangeROM.underHeader_fits header b (v i) _ _ env read r
  let V := amount (.fork header b) (.fork header (v i))
  change BoundedFits env _ (pile 0 (.fork header b) r) _ (105*V) (base+106*V) (106*V)
  have time : 84*header.count+90*b.count+11 ≤ 105*V := by dsimp [V,amount,Tree.count]; omega
  exact BoundedFits.of_fits (run.mono time)
    (fun j => by have := hb.pile 0 (.fork header b) j; dsimp only [V,amount,Tree.count] at *; omega)
    (by omega)

private theorem scaffoldRun {W : ℕ} (hw : 0 < W) {A : Type} (p : Series A)
    (v : Fin W → A → Tree) :
    let b := stripe (Series.natural W) (fun u => stripe p (v u))
    Run (scaffold 0) 441 442 b (b.fork (stripe p (fun _ => .atom false))) := by
  intro b env r base hb
  let i : Fin W := ⟨0,hw⟩
  have h := scaffold_fits (Series.natural W) p (fun x u => v u x) i env r
  change Fits _ (scaffold ((List.finRange W).idxOf i)) _ _ _ at h
  rw [List.idxOf_finRange] at h
  change Fits env (scaffold 0) _ _ (430*b.count+10) at h
  let V := amount b (b.fork (stripe p (fun _ => .atom false)))
  have time : 430*b.count+10 ≤ 441*V := by dsimp [V,amount,Tree.count]; omega
  exact BoundedFits.of_fits (h.mono time)
    (fun j => by have := hb.pile 0 b j; dsimp only [V,amount,Tree.count] at *; omega)
    (by change 441*V ≤ 442*V; omega)

noncomputable def openTime (W : ℕ) := chainCoeff ((W+1)*(chainCoeff 105 carveCoeff 1+100)) 441 1
noncomputable def openSpace := chainCoeff (chainCoeff 106 carveCoeff 1+70) 442 1

/-- Named physical run, including preservation of the shared row rulers while
selecting each column and construction of the blank prefix scaffold. Only
the time coefficient depends on the width of the bank. -/
theorem open_run {W : ℕ} (hw : 0 < W) {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp : 0 < p.count) (hd : 0 < d.count) (ht : 0 < t.count) (v : Fin W → (A × D) × T → Tree) :
      let rows := Series.natural W
      let input := Tree.fork (send (tally p.count,tally d.count,tally t.count))
        (stripe rows (fun i => stripe ((p.cart d).cart t) (v i)))
      let bank := stripe rows (fun i => stripe p (fun a => stripe d (fun j => stripe t (fun k => v i ((a,j),k)))))
      Run (openBank W) (openTime W) openSpace input (.fork bank (stripe p (fun _ => .atom false))) := by
  intro rows input bank
  let head := send (tally p.count,tally d.count,tally t.count)
  let flat (i : Fin W) := stripe ((p.cart d).cart t) (v i)
  let record (i : Fin W) (a : A) := stripe d (fun j => stripe t fun k => v i ((a,j),k))
  let nested (i : Fin W) := stripe p (record i)
  have lane (i : Fin W) : Run (openCell i.val) (chainCoeff 105 carveCoeff 1) (chainCoeff 106 carveCoeff 1) input (nested i) := by
    apply (selectRun head flat i).join (carve_run p d t hp hd ht (v i))
    have sub := cell_count rows flat i
    change (Tree.fork head (flat i)).count ≤ 1*amount (.fork head (stripe rows flat)) (nested i)
    simp only [one_mul,amount,Tree.count]
    omega
  apply (numeric_series openCell input nested lane).join (scaffoldRun hw p record)
  change bank.count ≤ 1 * amount input (.fork bank _)
  simp only [one_mul,amount,Tree.count]
  omega

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
