import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectLink
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectFinish
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound

/-! # Linking a generated tag table to its physical scalar actions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveScale
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelEffectiveFamily KernelPass Filter
open KernelPass.ComputableSyntax KernelScaleBank
open KernelScaleSpectator (expand)
open private tags tag_order bounds tagUnit tag_size list_vol bank_size
  from OAI.Computability.NearSquareRoot.KernelScaleBank

abbrev Params := ℕ × Op
abbrev Tags := ℕ × ℕ × List ℕ

def tagParams (p : Params) : Tags := (p.1,arg p.2 0,p.2.2.1.tail)
def test (p : Tags) := KernelComputableSelector.test (p.1+1) p.2.1 p.2.2

theorem computable_tagParams : Computable tagParams :=
  Computable.fst.pair ((primrec_arg.to_comp.comp Computable.snd (Computable.const 0)).pair
    (Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))))

/-- A generated numeric tag table with its run contract on all widths. -/
def TagRuns (p : Tags) (c : Cmd) :=
  TimedAt c (fun f => ((p.1+1)*f+1)*2^((p.1+1)*f)) (fun f => send (tally ((p.1+1)*f)))
    (fun f => send ((KernelSelector.addressColumns p.1 f).map (KernelScaleStream.tag (test p))))

/-- The core command sees the scale-specific shape header and the scalar
bank. Its syntax is independent of the descriptor or layout of its caller. -/
def CoreRuns (p : Params) (c : Cmd) := ∀ {I F : Type} (L : Layout p.1 I F) (w : I → ℕ)
    (x y : ∀ i, F → Dusk.Grain (w i)),
    (∀ i, ∀ z ∈ L.rows i, KernelScaleRecord.applyCoeff
      (KernelComputableSelector.table p.2.2.2 (signature L (test (tagParams p)) i z))
      (Dusk.mark (x i z)) = Dusk.mark (y i z)) →
    TimedAt c (volume L w) (fun i => send (header L i,bank L x i)) (fun i => send (bank L y i))

private theorem clock {a q : ℕ} {I F : Type} (L : Layout a I F)
    (test : Column (a+1) → Fin q → ZMod 2) (w : I → ℕ)
    (x : ∀ i, F → Dusk.Grain (w i)) (i : I) :
    let ns (i : I) := (tally (L.prefixCount i),tally (L.suffixCount i))
    let big (i : I) := expand (L.prefixCount i) (L.suffixCount i) (tags L test i)
    size (ns i) + (width L i+1)*2^(width L i) + L.prefixCount i*L.suffixCount i*size (tags L test i) +
      size (big i,bank L x i)+1 ≤ (2*tagUnit q+32)*(volume L w i+1) := by
  let ns (i : I) := (tally (L.prefixCount i),tally (L.suffixCount i))
  let big (i : I) := expand (L.prefixCount i) (L.suffixCount i) (tags L test i)
  obtain ⟨hN,hP,hS,hPS⟩ := bounds L i
  have hW := Nat.mul_le_mul_right (width L i+1) hN
  have sz := KernelScaleSpectator.size_expand (L.prefixCount i) (L.suffixCount i) (tags L test i)
  have tt : size (big i) ≤ tagUnit q * (L.rows i).length + 1 := by
    dsimp only [big]
    rw [tag_order L _ i]
    exact list_vol _ _ _ (fun _ => tag_size q _)
  have bb := bank_size L x i
  change size (ns i) + (width L i+1)*2^(width L i) +
    L.prefixCount i * L.suffixCount i * size (tags L test i) +
    size (big i,bank L x i) + 1 ≤ _
  change size (big i) + _ = _ at sz
  simp only [ns,size_prod,size_tally,tally_length]
  let V := (L.rows i).length * (width L i+w i+1)
  have rowV : (L.rows i).length ≤ V := Nat.le_mul_of_pos_right _ (by omega)
  have wV : (L.rows i).length * (w i+1) ≤ V := Nat.mul_le_mul_left _ (by omega)
  have gV : (width L i+1)*2^(width L i) ≤ V := by
    rw [Nat.mul_comm]
    exact hW.trans (Nat.mul_le_mul_left _ (by omega))
  have tV := Nat.mul_le_mul_left (tagUnit q) rowV
  have bV : size (bank L x i) ≤ 4*V + 4*V + 3 := by nlinarith only [bb,wV,rowV]
  change _ ≤ (2*tagUnit q+32)*(V+1)
  nlinarith only [tV,tt,sz,bV,gV,rowV,hP,hS,hPS]

/-- The emitter is a straight-line composition of an address scan, the
fixed spectator expansion, and the generated coefficient actions. -/
theorem core_family (tagsRun : ∀ᶠ R in atTop, ∃ c : Tags → Cmd, Effective ltr c ∧
    ∀ p, Within R (c p) ∧ TagRuns p (c p)) :
    ∀ᶠ R in atTop, ∃ c : Params → Cmd, Effective ltr c ∧ ∀ p, Within R (c p) ∧ CoreRuns p (c p) := by
  filter_upwards [eventually_ge_atTop 4,tagsRun,RegisterSelect.spectator_command,finish_family]
    with R hR ht he hf
  obtain ⟨tag,hTag,tRuns⟩ := ht
  obtain ⟨spect,C,sWithin,sRun⟩ := he
  obtain ⟨apply,hApply,aRuns⟩ := hf
  let choose (p : Params) := tag (tagParams p)
  let coef (p : Params) := apply p.2.2.2
  let source (p : Params) := (leftCmd ((rightCmd (choose p)).join spect)).join (coef p)
  have tg : Effective ltr choose := hTag.comp computable_tagParams
  have cf : Effective ltr coef := hApply.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  refine ⟨source,(effective_left ((effective_right tg).join (effective_const ltr spect))).join cf,?_⟩
  intro p
  obtain ⟨wTag,runTag⟩ := tRuns (tagParams p)
  obtain ⟨wApply,runApply⟩ := aRuns p.2.2.2
  refine ⟨⟨within_left (by omega) ⟨within_right (by omega) wTag,sWithin⟩,wApply⟩,?_⟩
  intro I F L w x y ok
  let t : Column (p.1+1) → Fin (arg p.2 0) → ZMod 2 := test (tagParams p)
  let s (i : I) := tags L t i
  let ns (i : I) := (tally (L.prefixCount i),tally (L.suffixCount i))
  let big (i : I) := expand (L.prefixCount i) (L.suffixCount i) (s i)
  have gen := TimedAt.on runTag (fun i => 2*L.h i)
  have exp : TimedAt spect (fun i => L.prefixCount i*L.suffixCount i*size (s i))
      (fun i => send (ns i,s i)) (fun i => send (big i)) :=
    ⟨C,fun i => sRun _ _ _ (L.prefix_pos i) (L.suffix_pos i)⟩
  have A := ((gen.right (fun i => send (ns i))).join exp).left (fun i => send (bank L x i))
  let raw (i : I) := ((big i).map unaryTag,bank L x i)
  have same (i : I) : finish p.2.2.2 (raw i) = bank L y i := by
    dsimp only [raw,big,s]
    rw [tag_order L _ i]
    simp only [List.map_map]
    apply finish_rows _ (L.rows i) _ (fun z => Dusk.mark (x i z)) (fun z => Dusk.mark (y i z)) (ok i)
  have B : TimedAt (coef p) (fun i => size (big i,bank L x i))
      (fun i => send (big i,bank L x i)) (fun i => send (bank L y i)) := by
    obtain ⟨D,hd⟩ := runApply
    refine ⟨D,fun i env => ?_⟩
    have v := hd (raw i) env
    rw [same] at v
    simpa only [raw,size,send_prod,tag_erase] using v
  exact (A.join B).bound _ fun i => clock L t w x i

end EffectiveScale

end NearSquareRoot
end Computability
end OAI
