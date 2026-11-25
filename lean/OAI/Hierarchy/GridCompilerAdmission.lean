import OAI.Hierarchy.GridControllerIdle
import OAI.Hierarchy.GridSelectorSwitch
import OAI.Hierarchy.GridCompilerEmitter
import OAI.Hierarchy.GridSelfHeader
import OAI.Hierarchy.GridAdmissionContinuation

namespace OAI
/-! # Loading X, admitted controller output and the physical contraction-image writer -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridCompilerAdmission
open ThreeFlat Diagonal RAM ContinuationLink PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM UniversalGrid GridThrough
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {w k n p e ell B limit : ℕ}
variable (X : Catalyst.Approximation F k p) (enc : FieldCode F (64*w))

variable {d tp tr tk ep er ek start : ℕ}
variable (params : Fin d → Word (64*w))
variable (receive : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
variable (x : GridDiagonal.Pins (Fin e)) (s : Bits ell)
local notation "pins" => (x ∘ Wiring.railPin.symm)
local notation "captured" => GridSelfHeader.captured (B:=B) X enc params receive eval pins start s
local notation "loaded" => GridApproximationAdvice.paddedMemory X enc B (2*GridDescription.sector w) captured
local notation "write" => GridOrderedSources.writing (arena w) k n p e B limit (Fintype.card F)
  (enc.encode 0) (enc.encode 1)

theorem admission (nav : Procedure (64*w)) (navTime : ℕ)
    (setting : Option (GridNativeEvaluator.Setting (e:=e) (n:=n) X))
    (large : 768≤w) (pos : 0<B)
    (rawRoom : GridSelfHeader.rawSize w e B d≤2^(4*w))
    (sep : GridSelfHeader.rawSize w e B d ≤ start)
    (fit : GridOrderedSources.Fits (n:=n) (r:=e) (w:=64*w) X (arena w) B)
    (selection : (arena w).railMap.Fits (64*w) k n e B)
    (padded : ∀ v, setting=some v → GridPaddedCellImage.Fits (w:=64*w) X (Ordered.wiring v)
      ((arena w).finalBanks limit))
    (size : GridApproximationAdvice.wordCount X≤12*B)
    (installed : ∀ v, setting=some v → v.pass=GridLens.firstPassage v.direction v.row v.touch
      X.width v.untouched_capacity)
    (source : TickStageSpec.Admission enc nav.block nav.publicData (·=loaded)
      (fun _ => setting.isSome) (fun _ out => ∀ v, setting=some v →
        GridOrderedSources.Raw X v enc (arena w) B pins out loaded) navTime) :
    let E := emit nav B n k p e limit (Fintype.card F) (enc.encode 0) (enc.encode 1)
    TickStageSpec.Admission enc E.block E.publicData (·=captured) (fun _ => setting.isSome)
      (fun _ out => ∀ v, setting=some v → ∀ i<BitLayout.footprint (GridNativeEvaluator.net X v),
        out i=BitLayout.memory (GridNativeEvaluator.net X v) enc pins (fun _=>false) i)
      (clock w k n e B limit navTime) := by
  let L := GridApproximationAdvice.loader w B (e*2+w^2) (2*GridDescription.sector w)
  let ok := fun _ : Memory (64*w) => setting.isSome=true
  let pre := fun m : Memory (64*w) => m=captured
  let ready := fun m : Memory (64*w) => ∀ v, setting=some v →
    GridOrderedSources.Raw X v enc (arena w) B pins m loaded
  let stored := fun out => ∃ tmp : Memory (64*w), tmp=loaded ∧ ready out
  have read : TickStageSpec.Admission enc (L.seq nav).block (L.seq nav).publicData pre ok
      (fun _ out=>stored out) (4000*(w*B)+navTime) :=
    TickStageSpec.admission_seq (good:=ok) enc L nav
      (TickStageSpec.admission_of_spec enc L
        (GridSelfHeader.loader X enc params receive eval pins large pos rawRoom sep s))
      source (fun _ _ _ => trivial) (fun _ _ _ _ h => ⟨h,Iff.rfl⟩)
  intro E
  refine GridNativeController.follow_read enc (L.seq nav) write captured setting stored
    (fun v out=>∀ i<BitLayout.footprint (GridNativeEvaluator.net X v),
      out i=BitLayout.memory (GridNativeEvaluator.net X v) enc pins (fun _=>false) i)
    (4000*(w*B)+navTime) (GridOrderedSources.clock k n e B limit) read ?_
  rintro v hv mid ⟨_,_,available⟩ pc regs slots M code reg pub exit text rom cfg m enter hmem
  subst m
  exact GridOrderedSources.writing_spec X v enc (arena w) B limit pins loaded fit selection
    (padded v hv) size (installed v hv) M code reg pub exit text rom cfg mid enter (available v hv)

section Selector
open GridControllerIdle ThreeFlat.Diagonal.HistoryContraction

variable {dim q S pc rc kc cap logRadix : ℕ}
variable (Y : Catalyst.Approximation F (dim+1) (q*S)) (hp : 0<pc) (reserved : ∀ j,Y.width j≤B)
variable {initial : HistoryContraction.Shape} (P : Plan F initial) (C : P.Codes) (bits : P.History → ℕ)
local notation "railCount" => ((dim+1)*GridIdleLayout.each dim n B)
local notation "shape" => GridControllerIdle.shape dim n B logRadix q S pc
local notation "ord" => arena w
local notation "idleProg" => GridIdleLayout.program (n:=n) (p:=q*S) Y.width reserved
  (GridIdleLayout.literal (q:=q) (S:=S) (w:=w) (r:=rc) (K:=kc) hp)
variable (pin : Fin (((dim+1)*GridIdleLayout.each dim n B)*2) → Bool) (sel : Fin (cap+1)→Bool)
local notation "before" => GridSelfHeader.captured (B:=B) Y enc params receive eval pin (12*(ord).J) sel
local notation "initialMem" => GridApproximationAdvice.paddedMemory Y enc B (2*(ord).J) before
local notation "record" => GridSelector.read P C bits cap (List.ofFn (Fin.tail sel))
variable (scheduled : GridSelector.Trace P bits →
  GridNativeEvaluator.Setting (e:=(dim+1)*GridIdleLayout.each dim n B) (n:=n) Y)
local notation "choice" => (fun a : Option (GridSelector.Trace P bits) => a.elim idleProg scheduled)
local notation "decode" => (GridSelector.decode P C bits cap sel).map choice

/-- The true external flag chooses one native branch. The compression side
reads the exact chronology and terminal grades. The other branch checks
every unused bit and writes the uniformly spaced literal-accepting grid. -/
theorem dispatch (sim : Procedure (64*w)) (simTime : ℕ)
    (fit : GridControllerIdle.Fits (64*w) ord shape) (room : GridControllerIdle.Room ord shape)
    (extent : GridApproximationAdvice.wordCount Y≤12*B) (compact : 12*B≤(ord).J)
    (capFit : cap<(ord).J) (upper : 13*(ord).J+3<2^(64*w))
    (low : GridSelfHeader.rawSize w railCount B d≤12*(ord).J)
    (simulate : sel 0=true → TickStageSpec.Admission enc sim.block sim.publicData (·=initialMem)
      (fun _ => (record).isSome) (fun _ out => ∀ z,record=some z →
        GridOrderedSources.Raw Y (scheduled z) enc ord B pin out initialMem) simTime) :
    let idle := GridControllerIdle.guarded (64*w) ord shape cap
    let nav := GridSelectorSwitch.program ((12*(ord).J:ℕ):Word (64*w)) idle sim
    TickStageSpec.Admission enc nav.block nav.publicData (·=initialMem) (fun _ => (decode).isSome)
      (fun _ out => ∀ v,decode=some v → GridOrderedSources.Raw Y v enc ord B pin out initialMem)
      (4+max (GridControllerIdle.guardedCost (64*w) ord shape cap) simTime) := by
  intro idle nav
  have below : 12*(ord).J<2^(64*w) := by omega
  have flag : initialMem (12*(ord).J) = BitLayout.bitWord (64*w) (sel 0) := by
    have keep : ¬(2*(ord).J≤12*(ord).J ∧ 12*(ord).J<2*(ord).J+12*B) := by omega
    simp only [GridApproximationAdvice.paddedMemory,fillSegment,ite_eq_right keep,GridSelfHeader.captured]
    simpa using GuessLoop.install_get (12*(ord).J) sel _ (0 : Fin (cap+1))
  have base : (((12*(ord).J:ℕ):Word (64*w))).val=12*(ord).J := Fin.val_cast_of_lt below
  have one : (1 : Word (64*w))≠0 := fun eq => by
    have h : 1<2^(64*w) := by omega
    have := congrArg Fin.val eq
    simp [Nat.mod_eq_of_lt h] at this
  intro pcs regs pubs machine pcEntry rgEntry pubEntry stop install values cfg0 mem0 here prior
  refine GridSelectorSwitch.admission enc ((12*(ord).J : ℕ) : Word (64*w)) idle sim
    (·=initialMem) (fun _ => (decode).isSome)
    (fun _ out => ∀ v, decode=some v → GridOrderedSources.Raw Y v enc ord B pin out initialMem)
    (GridControllerIdle.guardedCost (64*w) ord shape cap) simTime ?_ ?_
    machine pcEntry rgEntry pubEntry stop install values cfg0 mem0 here prior
  · intro p r K M pc rg pub exit inst data cfg mem atEntry pre
    obtain ⟨rfl,zero⟩ := pre
    rw [base,flag] at zero
    have branch : sel 0=false := by
      cases e0 : sel 0 with
      | false => rfl
      | true => exact False.elim (one (by simpa [e0,BitLayout.bitWord] using zero))
    obtain ⟨yes,no⟩ := GridControllerIdle.guarded_admission (r:=rc) (K:=kc) Y enc params receive eval
      ord hp reserved pin sel fit room extent compact capFit upper low
      M pc rg pub exit inst data cfg _ atEntry rfl
    by_cases live : ∀ i,Fin.tail sel i=false
    · obtain ⟨t,ht,d',out,endAt,src,walk⟩ := yes live
      refine ⟨fun _ => ⟨t,ht,d',out,endAt,?_,walk⟩,?_⟩
      · intro v ev
        have hv : idleProg=v := by simpa [GridSelector.decode,branch,live] using ev
        exact hv ▸ src
      · simp [GridSelector.decode,branch,live]
    · exact ⟨by simp [GridSelector.decode,branch,live],fun _ => no live⟩
  · intro p r K M pc rg pub exit inst data cfg mem atEntry pre
    obtain ⟨rfl,nonzero⟩ := pre
    rw [base,flag] at nonzero
    have branch : sel 0=true := by
      cases e0 : sel 0 with
      | true => rfl
      | false => exact False.elim (nonzero (by simp [e0,BitLayout.bitWord]))
    obtain ⟨yes,no⟩ := simulate branch M pc rg pub exit inst data cfg _ atEntry rfl
    cases selected : record with
    | none =>
      refine ⟨by simp [GridSelector.decode,branch,selected],fun _ => no (by simp [selected])⟩
    | some z =>
      obtain ⟨t,ht,d',out,endAt,src,walk⟩ := yes (by simp [selected])
      refine ⟨fun _ => ⟨t,ht,d',out,endAt,?_,walk⟩,by simp [GridSelector.decode,branch,selected]⟩
      intro v same
      have hv : scheduled z=v := by simpa [GridSelector.decode,branch,selected] using same
      exact hv ▸ src z selected

end Selector

end Hierarchy.GridCompilerAdmission
end

end OAI
