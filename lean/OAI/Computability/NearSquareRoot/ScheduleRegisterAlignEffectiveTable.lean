import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveMap
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffective
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.KernelSelectorStream

/-! # Effective generation of binary column tables

One fixed command enumerates full-width addresses, preserving leading zeroes.
Another fixed command reads the binary digits of an address. Compiling a
parameterised lookup into this traversal requires only command composition
and a list map; the resulting command file is computed from the same parameter.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveColumns
open IntegerMultiplication Code CommonRegisters GeneratorSyntax EffectiveTask Filter
open KernelSelectorAlign
open Adic (Raw shoots)

private theorem digit_size (i : Fin 2) : size i+1 ≤ 4 := by
  change size (tally i.val)+1 ≤ 4
  rw [size_tally,tally_length]
  omega

private theorem width_of_mem {t : Tally} {w : Raw 2} (h : w ∈ shoots 2 t) : w.length=t.length := by
  obtain ⟨x,rfl⟩ := (Strip.Series.elements ..).mp h
  exact Adic.length x

private theorem tabulate {F Y : Type} [Codec Y] (k : F → ℕ) (v : F → Raw 2 → Y)
    (gen one : Cmd) (generate : Runs gen (fun t : Tally => (t.length+1)*2^t.length)
      send (fun t => send (shoots 2 t)))
    (lookup : Runs one (fun u : {s : F × Raw 2 // s.2.length=k s.1} => k u.val.1)
      (fun u => send u.val.2) (fun u => send (v u.val.1 u.val.2))) :
    Runs (gen.join (EffectiveMap.program one)) (fun f => (k f+1)*2^k f)
      (fun f => send (tally (k f))) (fun f => send ((shoots 2 (tally (k f))).map (v f))) := by
  let words (f : F) := shoots 2 (tally (k f))
  let dom (f : F) : {s : F × List (Raw 2) // ∀ w∈s.2, w.length=k s.1} :=
    ⟨(f,words f),fun w hw => (width_of_mem hw).trans (tally_length _)⟩
  have many := (EffectiveMap.run one (fun _ : F => send (X:=Raw 2)) (fun f w => send (v f w))
    (fun f _ => k f) (fun f w => w.length=k f) lookup).on dom
  have output (f : F) :
      Task.forest (fun w => send (v f w)) (words f) = send ((words f).map (v f)) :=
    (Task.forest_map send (v f) _).symm.trans (Task.forest_send _)
  have scan : Runs (EffectiveMap.program one)
      (fun f => costSum (fun _ : Raw 2 => k f) (words f) + size (words f))
      (fun f => send (words f)) (fun f => send ((words f).map (v f))) :=
    many.conform (fun f => by simp [dom,size]) (fun f => by simp [dom]) (fun f => output f)
  have enumeration := generate.on (fun f : F => tally (k f))
  apply (enumeration.comp scan).bound 10
  intro f
  have sz := Adic.tally_bound 2 4 digit_size (tally (k f))
  have cc : costSum (fun _ : Raw 2 => k f) (words f) = 2^k f*k f := by
    simp [costSum,words,List.map_const']
  change ((tally (k f)).length+1)*2^(tally (k f)).length+
    (costSum (fun _ : Raw 2 => k f) (words f)+size (words f))+1 ≤ _
  rw [cc,tally_length]
  dsimp only [words]
  simp only [tally_length] at sz
  nlinarith [Nat.zero_le (2^k f)]

private theorem address_lookup (a : ℕ) {Y : Type} [Codec Y] (v : List (Column a) → Y)
    (readBits lookup : Cmd) (read : Runs readBits size (send (X:=Raw 2))
      (fun w => send (w.map KernelSelector.digitBit)))
    (one : Runs lookup List.length (fun xs => send (flatBits a xs)) (fun xs => send (v xs))) :
    Runs (readBits.join lookup) (fun u : {s : ℕ × Raw 2 // s.2.length=(a+1)*s.1} => (a+1)*u.val.1)
      (fun u => send u.val.2) (fun u => send (v (decode a u.val.1 (u.val.2.map KernelSelector.digitBit)))) := by
  let U := {s : ℕ × Raw 2 // s.2.length=(a+1)*s.1}
  let cs (u : U) := decode a u.val.1 (u.val.2.map KernelSelector.digitBit)
  have good (u : U) : (u.val.2.map KernelSelector.digitBit).length=(a+1)*u.val.1 := by simpa using u.property
  have cells := (one.on cs).conform
    (fun u : U => decode_length a u.val.1 _ (good u))
    (fun u : U => congrArg send (flatBits_decode a u.val.1 _ (good u))) (fun _ => rfl)
  have bits := read.on (fun u : U => u.val.2)
  apply (bits.comp cells).bound 6
  intro u
  have sz := Adic.raw_size 2 4 digit_size u.val.2
  rw [u.property] at sz
  have hs : u.val.1≤(a+1)*u.val.1 := Nat.le_mul_of_pos_left _ (by omega)
  change size u.val.2 + u.val.1+1 ≤ _
  omega

/-- The table program contains one fixed enumeration command and one compiled
list traversal. Its callback reads one full binary key and runs the supplied lookup. -/
def tableCommand (generator reader lookup : Cmd) : Cmd :=
  generator.join (EffectiveMap.program (reader.join lookup))

theorem tableCommand_effective {P : Type} [Primcodable P] (generator reader : Cmd)
    {lookup : P → Cmd} (h : Effective ltr lookup) :
    Effective ltr (fun p => tableCommand generator reader (lookup p)) :=
  (effective_const ltr generator).join (EffectiveMap.effective ((effective_const ltr reader).join h))

theorem tableCommand_within {R : ℕ} (hR : 3 ≤ R) {generator reader lookup : Cmd}
    (hg : Within R generator) (hr : Within R reader) (hl : Within R lookup) :
    Within R (tableCommand generator reader lookup) := ⟨hg,EffectiveMap.within hR ⟨hr,hl⟩⟩

theorem tableCommand_runs {Y : Type} [Codec Y] (a : ℕ) (v : List (Column a) → Y)
    {generator reader lookup : Cmd}
    (gen : Runs generator (fun t : Tally => (t.length+1)*2^t.length) send (fun t => send (shoots 2 t)))
    (read : Runs reader size (send (X:=Raw 2)) (fun w => send (w.map KernelSelector.digitBit)))
    (one : Runs lookup List.length (fun xs => send (flatBits a xs)) (fun xs => send (v xs))) :
    Runs (tableCommand generator reader lookup) (fun f => ((a+1)*f+1)*2^((a+1)*f))
      (fun f => send (tally ((a+1)*f))) (fun f => send ((KernelSelector.addressColumns a f).map v)) := by
  have h := tabulate (fun f => (a+1)*f) (fun f w => v (decode a f (w.map KernelSelector.digitBit)))
    generator (reader.join lookup) gen (address_lookup a v reader lookup read one)
  simpa only [tableCommand,KernelSelector.addressColumns,List.map_map,Function.comp_def] using h

/-- The register cutoff is independent of the parameter type, arity, tag
alphabet, and lookup program. The encoded lookup and its compiled table may
have parameter-dependent running-time constants. -/
theorem generateColumnTable : ∀ᶠ R : ℕ in atTop, ∀ {P : Type} [Primcodable P]
    (arity : P → ℕ) {Y : P → Type} [∀ p,Codec (Y p)] (v : ∀ p, List (Column (arity p)) → Y p),
    Family R (fun _ => List.length) (fun p xs => send (flatBits (arity p) xs)) (fun p xs => send (v p xs)) →
    Family R (fun p f => ((arity p+1)*f+1)*2^((arity p+1)*f))
      (fun p f => send (tally ((arity p+1)*f))) (fun p f => send ((KernelSelector.addressColumns (arity p) f).map (v p))) := by
  have bits := RegisterSelect.easy_eventually ((Code.Easy.finite KernelSelector.digitBit).mapping)
  have gen := RegisterSelect.checked_eventually (Adic.generate 2 (by decide))
  filter_upwards [bits,gen,eventually_ge_atTop 3] with R hbits hgen hR
  intro P _ arity Y _ v fam
  obtain ⟨reader,wr,hr⟩ := hbits
  obtain ⟨generator,wg,hg⟩ := hgen
  obtain ⟨lookup,effective,hlookup⟩ := fam
  refine ⟨fun p => tableCommand generator reader (lookup p),tableCommand_effective _ _ effective,?_⟩
  intro p
  obtain ⟨wl,hl⟩ := hlookup p
  exact ⟨tableCommand_within hR wg wr wl,tableCommand_runs _ _ hg hr hl⟩

/-- Compile directly from a lookup on aligned columns. Arity computation,
address enumeration, parsing, and repeated lookup are all included. -/
theorem tabulateColumnLookup : ∀ᶠ R : ℕ in atTop, ∀ {P : Type} [Primcodable P]
    (arity : P → ℕ) (_ : Computable arity) {Y : P → Type} [∀ p,Codec (Y p)]
    (v : ∀ p, List (Column (arity p)) → Y p),
    Family R (fun p => List.length (α := Column (arity p))) (fun _ => send) (fun p xs => send (v p xs)) →
    Family R (fun p f => ((arity p+1)*f+1)*2^((arity p+1)*f))
      (fun p f => send (tally ((arity p+1)*f))) (fun p f => send ((KernelSelector.addressColumns (arity p) f).map (v p))) := by
  filter_upwards [generateColumnTable,RegisterAlign.generate] with R table alignment
  intro P _ arity arityFile Y _ v lookup
  apply table arity v
  apply ((alignment.reindex arity arityFile).comp lookup).bound (fun _ => 2)
  intro p xs
  omega

end EffectiveColumns

end NearSquareRoot
end Computability
end OAI
