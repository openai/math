import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrection
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionBroadcast

/-! # Correction on the native header and the two live check banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters GeneratorSyntax InterchangeROMTable InterchangeROM

/-- Run the mask generator on a copy of the physical header. -/
def prependMask (emit : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass)
    ((clone 0 1 2).join (emit.join ((pack 0).join ((move 1 0 2).join (pack 0)))))

theorem prependMask_within {R : ℕ} (hR : 4 ≤ R) {emit : Cmd} (he : Within R emit) :
    Within R (prependMask emit) :=
  split_within (by omega) (fun _ => trivial)
    ⟨clone_within (by omega) (by omega) (by omega),he,(by omega : 0<R),move_within (by omega) (by omega) (by omega),(by omega : 0<R)⟩

theorem prependMask_fits (h parent mask : Tree) (emit : Cmd) (env : Env) (time : ℕ)
    (d : Deck)
    (he : Fits env emit (pile 0 h (pile 0 parent (pile 1 h d))) (pile 0 mask (pile 0 parent (pile 1 h d))) time) :
    Fits env (prependMask emit) (pile 0 (.fork h parent) d)
      (pile 0 (.fork h (.fork mask parent)) d) (time + 100*(h.count+1)) := by
  let park := pile 1 h d
  have save := fits_clone (i:=0) (j:=1) (u:=2) (by decide) (by decide) (by decide)
    h env (pile 0 parent d)
  rw [pile_comm 1 h d 0 parent (by decide)] at save
  have run := he
  have join := fits_pack mask parent park 0 env
  have restore := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) h env (pile 0 (.fork mask parent) d)
  rw [pile_comm 1 h d 0 _ (by decide)] at restore
  exact (fits_pair (save.join (run.join (join.join (restore.join (fits_pack ..)))))).mono (by omega)

/-- Duplicate the first data row while preserving its position in the bank. -/
private def pairScaffoldCore : Cmd :=
  splitRoot 0 (fun _ => .pass) ((move 0 3 2).join
    (splitRoot 0 (fun _ => .pass)
      ((clone 0 1 2).join ((pack 0).join ((move 1 0 2).join ((move 3 0 2).join (pack 0)))))))

private def pairScaffold : Cmd := pairScaffoldCore.join (pack 0)

private theorem pairScaffold_within : Within 4 pairScaffold :=
  ⟨
  split_within (by decide) (fun _ => trivial)
    ⟨move_within (by decide) (by decide) (by decide),split_within (by decide) (fun _ => trivial)
      ⟨clone_within (by decide) (by decide) (by decide),(by decide : 0<4),
        move_within (by decide) (by decide) (by decide),move_within (by decide) (by decide) (by decide),(by decide : 0<4)⟩⟩, (by decide : 0<4)⟩

private theorem pairScaffold_fits (mask head tail : Tree) (env : Env) (d : Deck) :
    Fits env pairScaffold (pile 0 (.fork mask (.fork head tail)) d)
      (pile 0 (.fork (.fork mask head) (.fork head tail)) d) (100*(mask.count+head.count+1)) := by
  let bank := Tree.fork head tail
  let deck := pile 3 mask d
  have park := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) mask env (pile 0 bank d)
  rw [pile_comm 3 mask d 0 _ (by decide)] at park
  have clone := fits_clone (i:=0) (j:=1) (u:=2) (by decide) (by decide) (by decide)
    head env (pile 0 tail deck)
  rw [pile_comm 1 head deck 0 tail (by decide)] at clone
  have pack := fits_pack head tail (pile 1 head deck) 0 env
  have take := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) head env (pile 0 bank deck)
  rw [pile_comm 1 head deck 0 bank (by decide)] at take
  have restore := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) mask env (pile 0 head (pile 0 bank d))
  rw [pile_comm 3 mask _ 0 head (by decide),pile_comm 3 mask d 0 bank (by decide)] at restore
  have saved := fits_pack mask head (pile 0 bank d) 0 env
  have final := fits_pack (.fork mask head) bank d 0 env
  have hs := fits_pair (c:=fun _=>.pass) (clone.join (pack.join (take.join (restore.join saved))))
  have hp := fits_pair (c:=fun _=>.pass) (park.join hs)
  exact ((hp.join final).mono (by omega))

/-- Keep the full bank below the amplification of its first payload row. -/
def widenHead : Cmd :=
  pairScaffold.join (splitRoot 0 (fun _=>.pass) (amplify.join (pack 0)))

theorem widenHead_within : Within 4 widenHead :=
  ⟨pairScaffold_within,split_within (by decide) (fun _=>trivial) ⟨amplify_within,(by decide : 0<4)⟩⟩

theorem widenHead_fits {A : Type} {P : A → Type} (tag : A → Tree) (v : (a : A) → P a → Tree)
    (rows : Series A) (payload : (a : A) → Series (P a)) (tail : Tree) (env : Env) (deck : Deck) :
    let narrow := stripe rows tag
    let row := stripe rows fun a => stripe (payload a) (v a)
    let wide := broadcast rows payload tag
    let bank := Tree.fork row tail
    Fits env widenHead (pile 0 (.fork narrow bank) deck) (pile 0 (.fork wide bank) deck)
      (700*(narrow.count+row.count+wide.count+1)) := by
  intro narrow row wide bank
  have prep := pairScaffold_fits narrow row tail env deck
  have copy := amplify_fits tag v rows.explore (fun a => (payload a).explore) env (pile 0 bank deck)
  simp only [← stripe_simple] at copy
  change Fits env amplify (pile 0 (.fork narrow row) (pile 0 bank deck))
    (pile 0 wide (pile 0 bank deck)) (500*(narrow.count+row.count+wide.count+1)) at copy
  exact (prep.join (fits_pair (copy.join (fits_pack wide bank deck 0 env)))).mono (by omega)

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
