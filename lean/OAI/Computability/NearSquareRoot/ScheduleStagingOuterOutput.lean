import OAI.Computability.NearSquareRoot.ScheduleStagingPublish
import OAI.Computability.NearSquareRoot.ScheduleStagingOuter

/-! # Literal output from the complete staged chunk controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingOuterOutput

open IntegerMultiplication TM Code Bits ChunkTask ChunkLoop ChunkPhases
open ChunkControl (Driver)
open StagingOuter (Axis Letter)

variable {I D : Type} (d : Driver)

def plain (s : StagingControl.Letter d) : Letter d := ((s,false,false),false)

def blank : Letter d := plain d none

def bit (b : Bool) : Letter d := plain d (some (Sum.inl (.bit b)))

def decode (a : Letter d) : Option Bool :=
  match a.1.1 with
  | some (.inl (.bit b)) => some b
  | _ => none

def source : Axis d I := .inl (ChunkDispatch.output (StagingOpen.cmd d))

/-- Register zero is positioned at its first product bit. The absolute
location and all three spatial marks are immaterial to the sequential read. -/
theorem final_read (C : ℕ) (p : Input) (w : Word) (j : ℕ) :
    decode d (((StagingOuter.final (I:=I) (D:=D) d C p (w.map Ltr.bit)).tape (source d)).view j)
      = w[j]? := by
  change (match ((w.map Ltr.bit).map (Sum.inl (β:=Prog.Ptr (ChunkDispatch.area (StagingOpen.cmd d)))))[j]? with
    | some (.inl (.bit b)) => some b
    | _ => none) = _
  simp only [List.getElem?_map]
  cases w[j]? <;> rfl

noncomputable def rule [DecidableEq I] (digit : Rule (Letter d) D (Axis d I)) (start : D) :=
  StagingPublish.rule (StagingOuter.driver d digit start).rule (source d) (decode d) (bit d)

noncomputable abbrev initial (C : ℕ) (p : Input) :=
  StagingPublish.active (blank d) (StagingOuter.initial (D:=D) (I:=I) d C p)

/-- A fixed rule with a dedicated fresh output tape. Its output agrees with
the raw bit word at every integer address, including all exterior addresses. -/
theorem run [DecidableEq I] (C : ℕ) (m : Operands → Word) (p : Input) (w : Word)
    (digit : Rule (Letter d) D (Axis d I)) (start : D) {T : ℕ}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p (w.map Ltr.bit))
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (call : ∀ i < p.count, StagingOuter.Call d C m p digit start T i) :
    let R := StagingOuter.radius C p.n
    ∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8)+1+w.length, ∃ z,
      FencedRun (rule d digit start) (fun _ => -(R : ℤ)-w.length-1)
        (fun _ => (R : ℤ)+w.length+1) (initial d C p) t z ∧
      advance (rule d digit start) z = none ∧ whole (blank d) (w.map (bit d)) (z.tape none) := by
  obtain ⟨t,ht,run,stop⟩ := StagingOuter.outer d C m p digit start ctl width call
  obtain ⟨z,tr,halt,out⟩ := StagingPublish.publish_fence _ (source d) (decode d) (bit d) (blank d)
    run stop w (final_read d C p w)
  exact ⟨_,by omega,z,tr,halt,out⟩

/-- Counting physical tape/address pairs gives a space coefficient independent
of the split, the input length and the digit clock. -/
theorem run_visited [DecidableEq I] [Fintype (Axis d I)] (C : ℕ) (m : Operands → Word)
    (p : Input) (w : Word) (hw : w.length = 2*p.n)
    (digit : Rule (Letter d) D (Axis d I)) (start : D) {T : ℕ}
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p (w.map Ltr.bit))
    (width : ∀ i < p.count, (digitReply m p i).length = 2*p.u)
    (call : ∀ i < p.count, StagingOuter.Call d C m p digit start T i) :
    ∃ t ≤ (p.count+1)*(6*(C*(p.n+1))+T+8)+1+2*p.n, ∃ z,
      Trace (advance (rule d digit start)) (initial d C p) t z ∧
      advance (rule d digit start) z = none ∧ whole (blank d) (w.map (bit d)) (z.tape none) ∧
      VisitsAtMost (rule d digit start) (initial d C p) t
        ((Fintype.card (Option (Axis d I)) * (2*(8*(C+50)+3)+1))*p.n) := by
  obtain ⟨t,ht,z,tr,halt,out⟩ := run d C m p w digit start ctl width call
  refine ⟨t,by omega,z,tr.1,halt,out,?_⟩
  have hn : 0 < p.n := p.positive.trans_le p.fits
  apply visitsAtMost_of_linear_fence _ _ hn
  intro u hu v hv i
  obtain ⟨lo,hi⟩ := tr.2 u hu v hv i
  have bigger : StagingOuter.radius C p.n + w.length + 1 ≤ (8*(C+50)+3)*p.n := by
    have h := Nat.mul_le_mul_left (4*(C+50)) (show p.n+1 ≤ 2*p.n by omega)
    dsimp only [StagingOuter.radius]
    rw [hw]
    nlinarith
  dsimp only at lo hi
  omega

end StagingOuterOutput

end NearSquareRoot
end Computability
end OAI
