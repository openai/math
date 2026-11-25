import OAI.Computability.BorderVNP.CubeISALocalRowImage

/-! # Real public power-table and declaration execution supplying the row checkers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall TeamContraction.JointHeader

/-- The three consecutive native components of the public scheduling assembly
responsible for powers, static secondary fields, and the compact declaration. -/
def publicBoot (n selectorBits : ℕ) : Code := .seq CubePowers.install (prepare n selectorBits)

/-- The real power and declaration programs, starting from the addressed
primary metadata and the common broadcast. Their return directly satisfies
the physical row setup ABI and supplies the true advertised row words. -/
theorem publicBoot_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (a : CubeArena.Layout) (saved : ℕ)
    (geometry : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (decl : Broadcast a.n a.header.d a.header.cap) :
    let raw := padded (TeamContraction.JointHeader.spelling (geometry++DeclarationBits.spelling decl) claims) pad
    let stat := a.header
    let dyn := stat.decoder saved
    let layout := rowLayout stat a.b a.h a.powerBase
    let width := selectorWidth a.n a.K a.h
    stat.Loaded (readings pub) (readings m) → stat.a = a.n+1 → stat.profile = geometry.length →
      frameField (readings pub) (readings m) 61 = a.h*a.b → frameField (readings pub) (readings m) 62 = a.powerBase →
      frameField (readings pub) (readings m) 25 = saved → FlatAt m saved raw →
      (pub 0).val+112 ≤ stat.header → saved+raw.length ≤ stat.header → 0 < stat.d →
      a.stop < 2^w → stat.d^(a.n+1) < 2^w → stat.Fits w a.n width (pub 0).val →
      HeaderDecode.Fits dyn w → stat.d*stat.d*stat.cap < 2^w →
      TestRun pub mac (publicBoot a.n width) r m
        ((16+5*(a.n+1))+(stat.cost a.n width+(HeaderDecode.cost dyn + HeaderTotals.cost (a.n+1) (stat.d*stat.d))))
        (readCode (a.n+1) decl.1 < a.n+1 ∧ ∀ pair j, readCode (stat.cap+1) (decl.2 pair j) < stat.cap+1)
        (fun z => z.mem = powerHeaderImage a saved (readings m) ∧
          layout.Loaded a.n (readings pub) z.mem ∧ z.mem stat.header = stat.header+13 ∧
          z.mem (stat.header+1) = stat.header+13+stat.entries ∧ z.mem (stat.header+5) = readCode (a.n+1) decl.1 ∧
          CubeLengths.StoredRows z.mem dyn.dense (fun pair j => readCode _ (decl.2 pair j)) ∧
          ∀ j : Fin (a.n+1), z.mem (dyn.totals+j.val) = ∑ pair, readCode _ (decl.2 pair j)) := by
  intro raw stat dyn layout width loaded axes profile bc powerPtr savedPtr copy before endCopy alphabet endRoom labels fit room sumRoom
  let pw := CubePowers.image stat.d a.powerBase (a.n+1) (readings m)
  have ex := arenaExtents a
  have away : stat.header+13 ≤ a.powerBase := by
    have ep : a.packetEnd+8+a.h ≤ a.powerBase := ex.2.1
    have sb : stat.header+13 ≤ stat.packetBase := by dsimp [stat,Inputs.packetBase]; omega
    have := ex.1
    change stat.packetBase ≤ a.packetEnd at this
    omega
  have powerRoom := ex.2.2.trans_lt endRoom
  have pri (k : ℕ) (hk : k < 112) : frameField (readings pub) pw k = frameField (readings pub) (readings m) k := by
    change pw ((pub 0).val+k) = _
    simp [pw,CubePowers.image,frameField,readings,show ¬a.powerBase ≤ (pub 0).val+k by omega]
  have state : stat.Loaded (readings pub) pw :=
    ⟨(pri 63 (by decide)).trans loaded.header,(pri 59 (by decide)).trans loaded.d,
     (pri 60 (by decide)).trans loaded.a,(pri 109 (by decide)).trans loaded.blocks,
     (pri 110 (by decide)).trans loaded.profile,(pri 111 (by decide)).trans loaded.cap⟩
  have powers := CubePowers.install_run pub mac r m stat.d (a.n+1) a.powerBase loaded.d
    (loaded.a.trans axes) powerPtr alphabet (by change (pub 0).val+62 < 2^w; have := fit.primary; omega) powerRoom labels
  apply ((powers.asTest (by decide)).seq (fun t mt eq => ?_)).mono le_rfl (by simp only [true_and]; exact Iff.rfl) (fun _ h => h)
  change readings mt = pw at eq
  have statLoaded : stat.Loaded (readings pub) (readings mt) := eq ▸ state
  have start : frameField (readings pub) (readings mt) 25 = saved := eq ▸ ((pri 25 (by decide)).trans savedPtr)
  have ini := install_run pub mac t mt stat statLoaded fit
  apply ((ini.asTest (install_deterministic ..)).seq (fun u mu image => ?_)).mono le_rfl (by simp only [true_and]; exact Iff.rfl) (fun _ h => h)
  change readings mu = stat.image a.n width (readings mt) at image
  have frame : HeaderDecode.AtFrame dyn (readings pub) (readings mu) :=
    image ▸ stat.decoder_at a.n width saved (readings pub) (readings mt) statLoaded start before
  have actual : FlatAt mu saved raw := by
    intro j
    apply Fin.ext
    change readings mu (saved+j.val) = _
    rw [image,eq]
    have early : saved+j.val < stat.header := by have := j.isLt; omega
    simp only [Inputs.image,ite_eq_right (show ¬(stat.header ≤ saved+j.val ∧ saved+j.val < stat.header+13) by omega)]
    rw [show pw (saved+j.val) = readings m (saved+j.val) from by
      simp [pw,CubePowers.image,show ¬a.powerBase ≤ saved+j.val by omega]]
    exact congrArg Fin.val (copy j)
  have dynEq : DeclarationBits.layout a.n stat.d stat.cap stat.header (saved+1+geometry.length)
      dyn.dense dyn.totals = dyn := by
    simp [DeclarationBits.layout,dyn,Inputs.decoder,axes,profile]
  have hw : 0 < w := by by_contra! hz; have h := room.small; simp [Nat.eq_zero_of_le_zero hz] at h
  have hHead : stat.header+12 < 2^w := by
    have hb := fit.bank
    change stat.header+13+2*stat.entries+stat.a < _ at hb
    omega
  have roomTotals : dyn.totals+(a.n+1) ≤ 2^w := by rw [← axes]; exact fit.bank.le
  have disjoint : dyn.dense+dyn.entries ≤ dyn.totals := by
    change stat.header+13+stat.entries+stat.entries ≤ stat.header+13+2*stat.entries
    omega
  have dhead : dyn.header+5 < dyn.totals := by
    change stat.header+5 < stat.header+13+2*stat.entries
    omega
  have good := DeclarationBits.program_from_copy decl geometry claims pad stat.header saved dyn.dense dyn.totals
    pub mac u mu actual hw (dynEq ▸ room) (dynEq ▸ frame) (by have := fit.primary; omega)
    hHead roomTotals (.inl (dynEq ▸ disjoint)) (.inl dhead) sumRoom
  rw [dynEq] at good
  apply good.mono le_rfl Iff.rfl
  rintro z ⟨out,coord,rows,sums⟩
  have exMem : z.mem = powerHeaderImage a saved (readings m) := by
    rw [out,image,eq]
    rfl
  obtain ⟨operands,h0,h1⟩ := loaded_of_powerHeader a (readings pub) saved (readings m) loaded axes bc powerPtr before
  exact ⟨exMem,exMem ▸ operands,exMem ▸ h0,exMem ▸ h1,coord,rows,sums⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
