import OAI.Computability.NearSquareRoot.InterchangeROMOuterSequence
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank

/-! # The emitted wiring for the physical row split and merge

The original center header is retained across the grouped stage. Its grouped
version goes to the cubic stage. Each endpoint regenerates its unary rulers
from the center header and the finite template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter.Wire

open IntegerMultiplication IntegerMultiplication.Code KernelEffectiveFamily GeneratorSyntax
  CommonRegisters InterchangeROM Space Filter

abbrev Rulers := Tree × Tree × Tree
private def duplicate (v : Tree × Tree) := (v.1,v)
private def entering (v : Rulers × (Tree × Tree)) := (v.2.1,v.1.2.2,v.1.1,v.2.2)
private def leaving (v : Rulers × (Tree × Tree × Tree)) := (v.2.1,v.1.2.1,v.2.2.2)

private theorem dup_easy : Easy duplicate := by unfold duplicate; fun_prop
private theorem enter_easy : Easy entering := by unfold entering; fun_prop
private theorem leave_easy : Easy leaving := by unfold leaving; fun_prop

def template (W b n : ℕ) := send (tally W,tally b,tally n)

def getRulers (W b n : ℕ) (rulers : Cmd) :=
  ((Task.prepare 0 (template W b n)).join (pack 0)).join rulers

noncomputable def prefixCmd (W b n : ℕ) (rulers : Cmd) :=
  dup_easy.choose.join (leftCmd (getRulers W b n rulers))

noncomputable def bank (W b n : ℕ) (rulers split : Cmd) :=
  ((prefixCmd W b n rulers).join enter_easy.choose).join (rightCmd (rightCmd split))

noncomputable def unbank (W b n : ℕ) (rulers merge : Cmd) :=
  ((prefixCmd W b n rulers).join leave_easy.choose).join (rightCmd merge)

private theorem effective_prefix {A : Type} [Primcodable A] (rulers : Cmd) {W b n : A → ℕ}
    (w : Computable W) (h : Computable b) (v : Computable n) :
    Effective ltr (fun a => prefixCmd (W a) (b a) (n a) rulers) := by
  have p0 : Effective ltr (fun x => Task.prepare 0 (send (tally (n x)))) := PhysicalWalshCompile.effective_tally_prepare.comp v
  have p1 : Effective ltr (fun x => Task.prepare 0 (send (tally (b x)))) := PhysicalWalshCompile.effective_tally_prepare.comp h
  have p2 : Effective ltr (fun x => Task.prepare 0 (send (tally (W x)))) := PhysicalWalshCompile.effective_tally_prepare.comp w
  have p := p0.join (p1.join (effective_const ltr (pack 0)))
  have t := p.join (p2.join (effective_const ltr (pack 0)))
  exact (effective_const ltr dup_easy.choose).join
    (effective_left ((t.join (effective_const _ (pack 0))).join (effective_const _ rulers)))

theorem effective_bank {A : Type} [Primcodable A] (rulers : Cmd) {W b n : A → ℕ} {split : A → Cmd}
    (w : Computable W) (h : Computable b) (v : Computable n) (s : Effective ltr split) :
    Effective ltr (fun a => bank (W a) (b a) (n a) rulers (split a)) :=
  ((effective_prefix rulers w h v).join (effective_const _ enter_easy.choose)).join
    (effective_right (effective_right s))

theorem effective_unbank {A : Type} [Primcodable A] (rulers : Cmd) {W b n : A → ℕ} {merge : A → Cmd}
    (w : Computable W) (h : Computable b) (v : Computable n) (s : Effective ltr merge) :
    Effective ltr (fun a => unbank (W a) (b a) (n a) rulers (merge a)) :=
  ((effective_prefix rulers w h v).join (effective_const _ leave_easy.choose)).join (effective_right s)

/-- One register cutoff suffices as the three loop parameters increase. -/
theorem registers (rulers : Cmd) : ∀ᶠ R : ℕ in atTop, ∀ W b n split merge,
    Within R split → Within R merge → Within R (bank W b n rulers split) ∧ Within R (unbank W b n rulers merge) := by
  filter_upwards [eventually_ge_atTop 3,RegisterSelect.within_eventually rulers,
    RegisterSelect.within_eventually dup_easy.choose,RegisterSelect.within_eventually enter_easy.choose,
    RegisterSelect.within_eventually leave_easy.choose] with R hr hd hc he hl W b n split merge hs hm
  have core : Within R (prefixCmd W b n rulers) :=
    ⟨hc,within_left (by omega)
      ⟨⟨(RegisterWitness.prepare_within _).mpr (by omega),(show 0 < R by omega)⟩,hd⟩⟩
  exact ⟨⟨⟨core,he⟩,within_right hr (within_right hr hs)⟩,⟨⟨core,hl⟩,within_right hr hm⟩⟩

/-- Local execution with an arbitrary finite height of already parked data. -/
def LocalFits (env : Env) (c : Cmd) (src dst : Tree) (t : ℕ) : Prop :=
  ∀ deck base, DeckCap base deck → Fits env c (pile 0 src deck) (pile 0 dst deck) t

private theorem underTag {env : Env} {c : Cmd} {x y : Tree} {t : ℕ} (tag : Tree)
    (run : LocalFits env c x y t) :
    LocalFits env (rightCmd c) (.fork tag x) (.fork tag y) (84*tag.count+t+11) := by
  intro d base live
  have left := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) tag env (pile 0 x d)
  have right := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) tag env (pile 0 y d)
  rw [pile_comm 1 _ d 0 _ (by decide)] at left right
  have middle := run (pile 1 tag d) _ (live.pile 1 tag)
  exact (fits_pair (left.join (middle.join (right.join (fits_pack ..))))).mono (by omega)

private theorem fits_prefix (W b n : ℕ) (rulers : Cmd) (tag data : Tree) (out : Rulers)
    (rt : ℕ) (env : Env)
    (run : LocalFits env rulers (.fork (template W b n) tag) (send out) rt) :
    LocalFits env (prefixCmd W b n rulers) (.fork tag data) (.fork (send out) (.fork tag data))
      (dup_easy.choose_spec.choose*(size (tag,data)+1)+5*(template W b n).count+rt+20) := by
  intro deck base live
  let saved := pile 0 (.fork tag data) deck
  have left := ((Task.fits_prepare 0 (template W b n) env (pile 0 tag saved)).join
    (fits_pack (template W b n) tag saved 0 env)).join (run saved _ (live.pile 0 (.fork tag data)))
  have formed := fits_pair (c:=fun _ => .pass) (left.join (fits_pack (send out) (.fork tag data) deck 0 env))
  exact ((dup_easy.choose_spec.choose_spec (tag,data) env deck).join formed).mono (by omega)

def work (tag raw : Tree) (out : Rulers) (W b n : ℕ) :=
  tag.count+raw.count+size out+(template W b n).count+1

/-- The split and compact-header generator contribute their actual clocks
once. The overhead scans only their local trees. -/
theorem fits_bank : ∃ K : ℕ, ∀ W b n rulers split tag raw banked (out : Rulers) rt bt env,
    LocalFits env rulers (.fork (template W b n) tag) (send out) rt →
    LocalFits env split (.fork out.1 raw) banked bt →
    LocalFits env (bank W b n rulers split) (.fork tag raw) (.fork tag (.fork out.2.2 banked))
      (K*work tag raw out W b n+rt+bt) := by
  let D := dup_easy.choose_spec.choose
  let E := enter_easy.choose_spec.choose
  refine ⟨4*D+5*E+250,?_⟩
  intro W b n rulers split tag raw banked out rt bt env rr rs deck base live
  have start := fits_prefix W b n rulers tag raw out rt env rr
  have next := enter_easy.choose_spec.choose_spec (out,tag,raw) env
  have outer := underTag tag (underTag out.2.2 rs) deck base live
  apply (((start deck base live).join (next deck)).join outer).mono
  have hs : out.2.2.count ≤ size out := by change out.2.2.count ≤ out.1.count+(out.2.1.count+out.2.2.count+1)+1; omega
  let M := work tag raw out W b n
  have x : size (tag,raw)+1 ≤ 4*M := by change tag.count+raw.count+1+1 ≤ 4*(tag.count+raw.count+size out+(template W b n).count+1); omega
  have y : size (out,tag,raw)+1 ≤ 5*M := by change (size out + (tag.count + raw.count + 1) + 1 + 1) ≤ 5*(tag.count+raw.count+size out+(template W b n).count+1); omega
  have dx := Nat.mul_le_mul_left D x
  have ey := Nat.mul_le_mul_left E y
  change D*_+_+rt+20 + E*_+2 + _+2 ≤ (4*D+5*E+250)*M+rt+bt
  rw [Nat.add_mul,Nat.add_mul]
  rw [show 4*D*M=D*(4*M) by ring,show 5*E*M=E*(5*M) by ring]
  dsimp [M,work] at *; omega

theorem fits_unbank : ∃ K : ℕ, ∀ W b n rulers merge tag grouped banked flat (out : Rulers) rt bt env,
    LocalFits env rulers (.fork (template W b n) tag) (send out) rt →
    LocalFits env merge (.fork out.2.1 banked) flat bt →
    LocalFits env (unbank W b n rulers merge) (.fork tag (.fork grouped banked)) (.fork tag flat)
      (K*work tag (.fork grouped banked) out W b n+rt+bt) := by
  let D := dup_easy.choose_spec.choose
  let E := leave_easy.choose_spec.choose
  refine ⟨4*D+5*E+250,?_⟩
  intro W b n rulers merge tag grouped banked flat out rt bt env rr rs deck base live
  have start := fits_prefix W b n rulers tag (.fork grouped banked) out rt env rr
  have next := leave_easy.choose_spec.choose_spec (out,tag,grouped,banked) env
  have outer := underTag tag rs deck base live
  apply (((start deck base live).join (next deck)).join outer).mono
  let M := work tag (.fork grouped banked) out W b n
  have x : size (tag,Tree.fork grouped banked)+1 ≤ 4*M := by change tag.count+(grouped.count+banked.count+1)+1+1 ≤ 4*(tag.count+(grouped.count+banked.count+1)+size out+(template W b n).count+1); omega
  have y : size (out,tag,grouped,banked)+1 ≤ 5*M := by change size out+(tag.count+(grouped.count+banked.count+1)+1)+1+1 ≤ 5*(tag.count+(grouped.count+banked.count+1)+size out+(template W b n).count+1); omega
  have dx := Nat.mul_le_mul_left D x
  have ey := Nat.mul_le_mul_left E y
  change D*_+_+rt+20 + E*_+2 + _+2 ≤ (4*D+5*E+250)*M+rt+bt
  rw [Nat.add_mul,Nat.add_mul]
  rw [show 4*D*M=D*(4*M) by ring,show 5*E*M=E*(5*M) by ring]
  dsimp [M,work] at *; omega

end InterchangeROMOuter.Wire

end NearSquareRoot
end Computability
end OAI
