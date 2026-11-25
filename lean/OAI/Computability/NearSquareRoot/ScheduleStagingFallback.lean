import OAI.Computability.NearSquareRoot.ScheduleStagingFallbackLayout
import OAI.Computability.NearSquareRoot.ScheduleStagingSource
import OAI.Computability.NearSquareRoot.ProductCanonical
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCandidate

/-! # The schoolbook fallback on exactly the shared public ports and alphabet -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingFallback

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open ChunkTask ChunkLoop ScheduleMachine

noncomputable section
open scoped Classical

local instance : Fintype school.A := Fintype.ofFinite _
local instance : Fintype school.I := Fintype.ofFinite _
local instance : DecidableEq school.I := Classical.decEq _

def code := oneHot (Fintype.equivFin school.A) school.blank

def decodeSchool (a : school.A) : Option Bool :=
  if a = school.bit true then some true else if a = school.bit false then some false else none

private theorem empty : decodeSchool school.blank = none := by
  simp [decodeSchool,(school.bits.2.1 true).2.symm,(school.bits.2.1 false).2.symm]

private theorem digits (b : Bool) : decodeSchool (school.bit b) = some b := by
  cases b <;> simp [decodeSchool,school.bits.1.ne Bool.false_ne_true]

abbrev PC := SourceControl school.A school.Q school.I code.width

def start : PC := sourceEntry school.A school.Q school.I code.width

def publicMachine : Rule Public.Letter PC (Pipeline.Index Private) :=
  sourceMachine code school.bit school.sep decodeSchool school.inp school.out school.machine school.beginState

def track (d : Driver) : StagingBank.Track Public.Letter (StagingProtection.Cell d) :=
  ⟨read d,fun _ a => embed d a⟩

def frame (d : Driver) : StagingBank.Frame (track d) (Pipeline.Index Private) :=
  ⟨fun _ => 0,fun _ _ => embed d,fun _ _ => read_embed d,fun _ _ _ _ => rfl⟩

def machine (d : Driver) (I : Type) : Rule (StagingProtection.Cell d) PC (Axes d I) :=
  StagingBank.rule (schoolRoute d I) (track d) publicMachine

def ports (d : Driver) (I : Type) : GeneratorInputRun.Ports (StagingProtection.Cell d) (Axes d I) where
  inp := inp d I
  out := out d I
  blank := StagingProtection.blank d
  sep := StagingSerialize.put d .sep
  bit := StagingProtection.bit d
  decode a := (read d a).join
  distinct := by intro h; cases h
  letters := by
    refine ⟨?_,?_,?_⟩
    · intro a b h
      exact Option.some.inj (Option.some.inj (congrArg (read d) h))
    · intro b
      constructor <;> intro h <;> cases h
    · intro h
      cases h
  decoding := ⟨rfl,fun _ => rfl⟩

private theorem from_input (x y : List Bool) :
    initialConfig school.beginState school.inp school.bit school.sep school.blank x y =
    loadedConfig school.beginState school.blank (sourceLoad school.bit school.sep school.inp x y) := by
  apply congrArg (Config.mk _)
  funext j
  by_cases eq : j = school.inp <;>
    simp [sourceLoad,load,srcWord,eq]

private theorem raw : StagingSource.Computes school.machine school.beginState school.blank school.sep school.bit
    school.inp school.out Lea.answer (fun n => school.time*n^2) (fun n => school.space*n) := by
  intro a
  obtain ⟨u,hx,hy⟩ := exists_input a.val.1.length a.property.2 a.val.1 a.val.2 rfl a.property.1.symm
  obtain ⟨t,z,w,h,stop,out,width,val,ht,hs⟩ := school.runs _ u
  rw [hx,hy,from_input] at h hs
  rw [hx,hy] at val
  have word := (ProductRecovery.product_postcondition_iff a.val.1 a.val.2 w rfl a.property.1.symm).mp ⟨width,val⟩
  exact ⟨t,ht,z,h,stop,word ▸ out,hs⟩

def time := 32*(code.width+1)*(school.time+3)+1
def space := (48*(code.width+1)+3*Fintype.card (Pipeline.Index Private))*(school.space+2)

private theorem literal (a : EqualWords) :
    ∃ t z, t+1 ≤ time*(a.val.1.length+1)^2 ∧
      Trace (advance publicMachine) ⟨start,publicLoad a.val.1 a.val.2⟩ t z ∧
      advance publicMachine z = none ∧ z.tape (.inl true) = Tape.loaded none ((Lea.answer a.val).map Public.bit) ∧
      VisitsAtMost publicMachine ⟨start,publicLoad a.val.1 a.val.2⟩ t (space*(a.val.1.length+1)) := by
  have c := StagingSource.computes code school.bit school.sep school.blank (oneHot_blank ..) decodeSchool empty digits
    school.inp school.out school.machine school.beginState Lea.answer _ _ raw (fun _ => Lea.date_length _)
  obtain ⟨t,ht,z,h,halt,out,vis⟩ := c a
  refine ⟨t,z,?_,h,halt,out,?_⟩
  · unfold time
    have h := Nat.mul_le_mul_left (32*(code.width+1))
      (show school.time*a.val.1.length^2+a.val.1.length+1 ≤ (school.time+3)*(a.val.1.length+1)^2 by nlinarith)
    rw [←Nat.mul_assoc] at h
    nlinarith
  · obtain ⟨cells,count,cover⟩ := vis
    refine ⟨cells,count.trans ?_,cover⟩
    unfold space
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)

def parked (d : Driver) (I : Type) (x : Config Public.Letter PC (Pipeline.Index Private)) :=
  StagingBank.parked (schoolRoute d I) (frame d) (fun _ => Tape.loaded (StagingProtection.blank d) []) x

private theorem mapped (d : Driver) (i : Pipeline.Index Private) (xs : List Public.Letter) :
    StagingBank.tape (frame d) i (Tape.loaded none xs) =
      Tape.loaded (StagingProtection.blank d) (xs.map (embed d)) := by
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  refine ⟨rfl,funext fun j => ?_⟩
  cases j with
  | negSucc => rfl
  | ofNat k =>
    change embed d (xs[k]?.getD none) = ((xs.map (embed d))[k]?).getD _
    rw [List.getElem?_map]
    cases xs[k]? <;> rfl

private theorem initial (d : Driver) (I : Type) (x y : List Bool) :
    parked d I ⟨start,publicLoad x y⟩ = initialConfig start (inp d I) (StagingProtection.bit d)
      (StagingSerialize.put d .sep) (StagingProtection.blank d) x y := by
  change Config.mk _ _ = Config.mk _ _
  rw [Config.mk.injEq]
  refine ⟨rfl,funext fun j => ?_⟩
  change ((parked d I ⟨start,publicLoad x y⟩).tape j) = (initialConfig start (inp d I) (StagingProtection.bit d) (StagingSerialize.put d .sep) (StagingProtection.blank d) x y).tape j
  by_cases active : ∃ i, (schoolRoute d I).index i = j
  · obtain ⟨i,rfl⟩ := active
    rw [parked,StagingBank.inside]
    rcases i with (_|_)|s
    · change StagingBank.tape _ _ (Tape.loaded none (rawWord x y)) = (initialConfig ..).tape (inp d I)
      simp only [initialConfig,ite_true,mapped,rawWord,List.map_append,List.map_cons,List.map_map,List.append_assoc,List.singleton_append]
      rfl
    · change StagingBank.tape _ _ (Tape.loaded none []) = (initialConfig ..).tape (out d I)
      simp [initialConfig,out,inp,mapped]
    · change StagingBank.tape _ _ (Tape.loaded none []) = (initialConfig ..).tape (Sum.inr s)
      simp [initialConfig,inp,mapped]
  · rw [parked,StagingBank.off _ _ _ _ _ active]
    have h : j ≠ inp d I := by rintro rfl; exact active ⟨.inl false,rfl⟩
    simp [initialConfig,h]

/-- The polynomial fallback starts on the same literal operands as every
generated positive candidate, with all other tapes blank. -/
theorem runs (d : Driver) (I : Type) (n : ℕ) (u : ScheduleMachine.Input n) :
    let p := ports d I
    let x := xbits u
    let y := ybits u
    ∃ t z, t+1 ≤ time*(n+1)^2 ∧ FencedRun (machine d I) (fun _ => -((space*(n+1):ℕ):ℤ))
        (fun _ => ((space*(n+1):ℕ):ℤ)) (initialConfig start p.inp p.bit p.sep p.blank x y) t z ∧
      advance (machine d I) z = none ∧ z.tape p.out = Tape.loaded p.blank ((Lea.answer (x,y)).map p.bit) := by
  let a : EqualWords := ⟨(xbits u,ybits u),by simp,by simpa using u.property⟩
  obtain ⟨t,z,ht,path,halt,outWord,vis⟩ := literal a
  have size : a.val.1.length = n := xbits_length u
  rw [size] at ht vis
  have tr := StagingBank.run (schoolRoute d I) (track d) (frame d)
    (fun _ => Tape.loaded (StagingProtection.blank d) []) publicMachine path
  have hf := StagingBank.halt (schoolRoute d I) (track d) (frame d)
    (fun _ => Tape.loaded (StagingProtection.blank d) []) publicMachine halt
  have init : parked d I ⟨start,publicLoad (xbits u) (ybits u)⟩ =
      initialConfig start (ports d I).inp (ports d I).bit (ports d I).sep (ports d I).blank (xbits u) (ybits u) :=
    initial d I _ _
  refine ⟨t,parked d I z,ht,⟨?_,?_⟩,hf,?_⟩
  · rw [← init]
    exact tr
  · intro k hk v prefixRun j
    rw [← init] at prefixRun
    obtain ⟨along,off⟩ := StagingBank.prefix_bounds (schoolRoute d I) (track d) (frame d)
      (fun _ => Tape.loaded (StagingProtection.blank d) []) publicMachine path vis hk prefixRun
    by_cases h : ∃ i, (schoolRoute d I).index i = j
    · obtain ⟨i,rfl⟩ := h
      simpa only [frame,StagingCall.initial_heads,Config.tape,zero_add,zero_sub] using along i
    · rw [off j h]
      change -((space*(n+1):ℕ):ℤ) ≤ 0 ∧ (0:ℤ) ≤ ((space*(n+1):ℕ):ℤ)
      have h : (0:ℤ) ≤ ((space*(n+1):ℕ):ℤ) := Int.natCast_nonneg _
      exact ⟨by omega,h⟩
  · change (parked d I z).tape ((schoolRoute d I).index (.inl true)) = _
    rw [parked,StagingBank.inside,outWord,mapped,List.map_map]
    rfl

end
end StagingFallback

end NearSquareRoot
end Computability
end OAI
