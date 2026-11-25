import OAI.Hierarchy.DescentDatedOperandMeasuredRead

namespace OAI
/-! # Exact eight-column result of the entire original-source selection program -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry)
local notation "A" => Values g g.digitBits
local notation "M" => g.lanes
local notation "J" => g.jobs
local notation "P" => g.paths
local notation "B" => g.blocks
local notation "D" => g.degree
local notation "C" => g.cap
local notation "a" => g.digitBits
structure Data (g : Geometry) where
  origin : Fin g.jobs → Fin 6 → Values g g.digitBits
  prior : Fin g.jobs → Fin 4 → Values g g.digitBits
  mouth : Fin g.jobs → Fin 3 → Values g g.digitBits
  old : Fin g.jobs → Fin 4 → Fin (g.paths*(g.blocks*(g.degree*g.cap))) → Values g g.digitBits
  path : Fin (g.paths*(g.degree+1)) → Values g g.digitBits
  anchor : Fin g.jobs → Fin 5 → Fin (g.paths*(g.blocks*(g.cap*3))) → Values g g.digitBits
  raw : Fin g.jobs → Fin 8 → Fin (g.paths*(g.blocks*(g.cap*11))) → Values g g.digitBits
  rank : Fin g.paths → Values g g.digitBits
variable (s : Sources g) (v : Data g)

structure Recorded {w : ℕ} (base : ℕ) (m : Memory w) : Prop where
  origin : ∀j f,Held g base m (s.origin j f) (v.origin j f)
  prior : ∀j f,Held g base m (s.prior j f) (v.prior j f)
  mouth : ∀j f,Held g base m (s.mouth j f) (v.mouth j f)
  old : ∀j f i,Held g base m (s.old j f i) (v.old j f i)
  path : ∀i,Held g base m (s.path i) (v.path i)
  anchor : ∀j f i,Held g base m (s.anchor j f i) (v.anchor j f i)
  raw : ∀j f i,Held g base m (s.raw j f i) (v.raw j f i)
  rank : ∀i,Held g base m (s.rank i) (v.rank i)

theorem Recorded.later {w lo hi : ℕ} {m : Memory w} {p : NativePhase w}
    (seen : Recorded g s v lo m) (run : Step lo hi p m) : Recorded g s v hi (p.image m) :=
  ⟨fun j f=>Step.keep g run (seen.origin j f),
   fun j f=>Step.keep g run (seen.prior j f),
   fun j f=>Step.keep g run (seen.mouth j f),
   fun j f i=>Step.keep g run (seen.old j f i),
   fun i=>Step.keep g run (seen.path i),
   fun j f i=>Step.keep g run (seen.anchor j f i),
   fun j f i=>Step.keep g run (seen.raw j f i),
   fun i=>Step.keep g run (seen.rank i)⟩

def oldInputs (j : Fin J) : Fin 6 → A :=
  ![v.origin j 0,v.prior j 0,v.origin j 1,v.origin j 2,v.prior j 1,v.prior j 2]
def oldV := picked g (oldLaw P B D C a) (oldInputs g v) v.old

def pathInputs (j : Fin J) : Fin 5 → A :=
  ![v.origin j 0,v.origin j 1,oldV g v j 3,oldV g v j 1,oldV g v j 2]
def pathV := picked g (pathLaw P D a) (pathInputs g v) (fun _ (_ : Fin 1)=>v.path)

def anchorInputs (j : Fin J) : Fin 9 → A :=
  ![v.origin j 0,v.prior j 0,v.origin j 1,pathV g v j 0,v.origin j 2,oldV g v j 3,oldV g v j 2,v.origin j 4,v.mouth j 0]
def anchorV := picked g (anchorLaw P B C a) (anchorInputs g v) v.anchor

def rawInputs (j : Fin J) : Fin 5 → A :=
  ![v.origin j 0,v.origin j 1,pathV g v j 0,anchorV g v j 4,v.mouth j 1]
def rawV := picked g (rawLaw P (B*(C*11)) a) (rawInputs g v) v.raw

def rankInputs (j : Fin J) : Fin 3 → A :=
  ![v.origin j 0,v.prior j 0,v.origin j 1]
def rankV := picked g (localLaw P a) (rankInputs g v) (fun _ (_ : Fin 1)=>v.rank)

def finalInputs (j : Fin J) : Fin 17 → A :=
  ![v.origin j 0,v.prior j 0,rankV g v j 0,v.origin j 2,v.origin j 1,pathV g v j 0,rawV g v j 6,rawV g v j 7,v.mouth j 1,anchorV g v j 0,anchorV g v j 1,anchorV g v j 2,anchorV g v j 4,rawV g v j 2,rawV g v j 3,rawV g v j 4,rawV g v j 5]

theorem after_ge (base n cols count : ℕ) : base≤after g n cols count base :=
  (show base≤DescentDatedOperandSelectionRun.nextAddress (layout g cols count) 1 n a base from Nat.le_add_right ..).trans
    (DescentDatedOperandSelectionRun.reaches _ base)

theorem observed {base w : ℕ} (m : Memory w) (data : Recorded g s v base m) (space : endAddress g base<2^w) :
    let run:=phase g s base w
    Step base (endAddress g base) run m ∧ ∀j f,
      Held g (endAddress g base) (run.image m) (expression g s base j f)
        (fun h k=>finalLaw g f (fun i=>finalInputs g v j i h k)) :=by
  intro run
  have frameEnd : finalBase g base≤endAddress g base:=Nat.le_add_right ..
  have h5 : finalBase g base<2^w:=frameEnd.trans_lt space
  have h4 : rankBase g base<2^w:=(after_ge g (rankBase g base) 3 1 (P)).trans_lt h5
  have h3 : rawBase g base<2^w:=(after_ge g (rawBase g base) 5 8 (P*(B*(C*11)))).trans_lt h4
  have h2 : anchorBase g base<2^w:=(after_ge g (anchorBase g base) 9 5 (P*(B*(C*3)))).trans_lt h3
  have h1 : pathBase g base<2^w:=(after_ge g (pathBase g base) 5 1 (P*(D+1))).trans_lt h2
  have input1 (j i) : Held g (base) m (oldArgs g s j i) (oldInputs g v j i) :=by
    fin_cases i <;> first
    | exact data.origin j 0
    | exact data.prior j 0
    | exact data.origin j 1
    | exact data.origin j 2
    | exact data.prior j 1
    | exact data.prior j 2
  have step1:=selection g (oldLaw P B D C a) (oldArgs g s) s.old (oldInputs g v)
    v.old m (old_dead P B D C a) input1 data.old h1
  let m1:=(oldPhase g s base w).image m
  have data1:=Recorded.later g s v data step1.1
  have oldHold1 (j : Fin J) (f : Fin 4):=step1.2 j f
  have input2 (j i) : Held g (pathBase g base) m1 (pathArgs g s base j i) (pathInputs g v j i) :=by
    fin_cases i <;> first
    | exact data1.origin j 0
    | exact data1.origin j 1
    | exact oldHold1 j 3
    | exact oldHold1 j 1
    | exact oldHold1 j 2
  have step2:=selection g (pathLaw P D a) (pathArgs g s base) (fun _ (_ : Fin 1)=>s.path) (pathInputs g v)
    (fun _ (_ : Fin 1)=>v.path) m1 (path_dead P D a) input2 (fun _ _ i=>data1.path i) h2
  let m2:=(pathPhase g s base w).image m1
  have data2:=Recorded.later g s v data1 step2.1
  have oldHold2 (j : Fin J) (f : Fin 4):=Step.keep g step2.1 (oldHold1 j f)
  have pathHold2 (j : Fin J) (f : Fin 1):=step2.2 j f
  have input3 (j i) : Held g (anchorBase g base) m2 (anchorArgs g s base j i) (anchorInputs g v j i) :=by
    fin_cases i <;> first
    | exact data2.origin j 0
    | exact data2.prior j 0
    | exact data2.origin j 1
    | exact pathHold2 j 0
    | exact data2.origin j 2
    | exact oldHold2 j 3
    | exact oldHold2 j 2
    | exact data2.origin j 4
    | exact data2.mouth j 0
  have step3:=selection g (anchorLaw P B C a) (anchorArgs g s base) s.anchor (anchorInputs g v)
    v.anchor m2 (anchor_dead P B C a) input3 data2.anchor h3
  let m3:=(anchorPhase g s base w).image m2
  have data3:=Recorded.later g s v data2 step3.1
  have oldHold3 (j : Fin J) (f : Fin 4):=Step.keep g step3.1 (oldHold2 j f)
  have pathHold3 (j : Fin J) (f : Fin 1):=Step.keep g step3.1 (pathHold2 j f)
  have anchorHold3 (j : Fin J) (f : Fin 5):=step3.2 j f
  have input4 (j i) : Held g (rawBase g base) m3 (rawArgs g s base j i) (rawInputs g v j i) :=by
    fin_cases i <;> first
    | exact data3.origin j 0
    | exact data3.origin j 1
    | exact pathHold3 j 0
    | exact anchorHold3 j 4
    | exact data3.mouth j 1
  have step4:=selection g (rawLaw P (B*(C*11)) a) (rawArgs g s base) s.raw (rawInputs g v)
    v.raw m3 (raw_dead P (B*(C*11)) a) input4 data3.raw h4
  let m4:=(rawPhase g s base w).image m3
  have data4:=Recorded.later g s v data3 step4.1
  have oldHold4 (j : Fin J) (f : Fin 4):=Step.keep g step4.1 (oldHold3 j f)
  have pathHold4 (j : Fin J) (f : Fin 1):=Step.keep g step4.1 (pathHold3 j f)
  have anchorHold4 (j : Fin J) (f : Fin 5):=Step.keep g step4.1 (anchorHold3 j f)
  have rawHold4 (j : Fin J) (f : Fin 8):=step4.2 j f
  have input5 (j i) : Held g (rankBase g base) m4 (rankArgs g s j i) (rankInputs g v j i) :=by
    fin_cases i <;> first
    | exact data4.origin j 0
    | exact data4.prior j 0
    | exact data4.origin j 1
  have step5:=selection g (localLaw P a) (rankArgs g s) (fun _ (_ : Fin 1)=>s.rank) (rankInputs g v)
    (fun _ (_ : Fin 1)=>v.rank) m4 (local_dead P a) input5 (fun _ _ i=>data4.rank i) h5
  let m5:=(rankPhase g s base w).image m4
  have data5:=Recorded.later g s v data4 step5.1
  have oldHold5 (j : Fin J) (f : Fin 4):=Step.keep g step5.1 (oldHold4 j f)
  have pathHold5 (j : Fin J) (f : Fin 1):=Step.keep g step5.1 (pathHold4 j f)
  have anchorHold5 (j : Fin J) (f : Fin 5):=Step.keep g step5.1 (anchorHold4 j f)
  have rawHold5 (j : Fin J) (f : Fin 8):=Step.keep g step5.1 (rawHold4 j f)
  have rankHold5 (j : Fin J) (f : Fin 1):=step5.2 j f
  have final (j i) : Held g (finalBase g base) m5 (finalArgs g s base j i) (finalInputs g v j i) :=by
    fin_cases i <;> first
    | exact data5.origin j 0
    | exact data5.prior j 0
    | exact rankHold5 j 0
    | exact data5.origin j 2
    | exact data5.origin j 1
    | exact pathHold5 j 0
    | exact rawHold5 j 6
    | exact rawHold5 j 7
    | exact data5.mouth j 1
    | exact anchorHold5 j 0
    | exact anchorHold5 j 1
    | exact anchorHold5 j 2
    | exact anchorHold5 j 4
    | exact rawHold5 j 2
    | exact rawHold5 j 3
    | exact rawHold5 j 4
    | exact rawHold5 j 5
  have last:=DescentOperandFamilyBook.any (finalLaw g) M (finalBase g base) m5 space
  have tail:Step (finalBase g base) (endAddress g base) (bankPhase g base w) m5:=⟨frameEnd,last.1,last.2.2.1⟩
  refine ⟨(((((step1.1.thenStep step2.1).thenStep step3.1).thenStep step4.1).thenStep step5.1).thenStep tail),?_⟩
  intro j f
  have issued:=DescentOperandFamilyBook.issued (finalLaw g) (final_dead g) M (finalBase g base) f (finalArgs g s base j)
    m5 (fun h k i=>finalInputs g v j i h k) (fun i=>(final j i).fits) (fun i=>(final j i).read) space
  exact ⟨issued.1,issued.2⟩

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
