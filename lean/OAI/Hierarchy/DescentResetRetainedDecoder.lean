import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentPackedNodeDigit
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Decode a compact chronological donor position and its first local hidden occurrence -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (v : Layout)

def entry (word : Cell v.siteWord) (d : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) : Cell v.bits :=
  let c:=finProdFinEquiv (f,n)
  let part:=(encode v.stripWord v.channels).symm word c
  (encode v.bits v.donors).symm part d
def originalCount (word : Cell v.siteWord) (d : Fin v.donors) : ℕ :=
  ∑n : Fin v.previousNodes,if (v.entry word d n v.occupiedField).val=0 then 0 else 1
def offset (word : Cell v.siteWord) (d : Fin v.donors) : ℕ :=
  ProtocolRAMPortRanks.«prefix» (v.originalCount word) Fin.val d
def owns (word : Cell v.siteWord) (node : ℕ) (d : Fin v.donors) : Prop :=
  v.offset word d≤node ∧ node<v.offset word d+v.originalCount word d
def root (word : Cell v.siteWord) (node : ℕ) : Option (Fin v.donors) :=
  (List.finRange v.donors).find? (fun d=>decide (v.owns word node d))
def location (word : Cell v.siteWord) (node arg : ℕ) :
    Option (Fin v.donors×Fin v.previousNodes×Fin v.previousArgs) :=
  (v.root word node).bind fun d=>
    let earlier:=node-v.offset word d
    if hn:earlier<v.previousNodes then
      let n:Fin v.previousNodes:=⟨_,hn⟩
      if ha:arg<v.previousArgs then
        if arg<(v.entry word d n v.arityField).val then some (d,n,⟨_,ha⟩) else none
      else none
    else none
def rawField (word : Cell v.siteWord) (node arg : ℕ) (f : Fin 7) : Cell v.bits :=
  (v.location word node arg).elim 0 (fun z=>v.entry word z.1 z.2.1 (v.operandField f z.2.2))
def keyAt (word : Cell v.siteWord) (node arg : ℕ) : Option (Fin v.donors×Cell v.bits) :=
  (v.location word node arg).bind fun z=>
    if (v.entry word z.1 z.2.1 (v.operandField 0 z.2.2)).val=0 then
      some (z.1,v.entry word z.1 z.2.1 (v.operandField 2 z.2.2))
    else none
def keyIndex (word : Cell v.siteWord) (i : Fin (v.nodes*v.args)) :=
  let p:=(finProdFinEquiv.symm i : Fin v.nodes×Fin v.args)
  v.keyAt word p.1.val p.2.val
def leastSlot (word : Cell v.siteWord) (key : Fin v.donors×Cell v.bits) : ℕ :=
  if found : ∃n : ℕ,∃i : Fin (v.nodes*v.args),i.val=n ∧ v.keyIndex word i=some key then
    Nat.find found else 0
def localName (word : Cell v.siteWord) (node arg : ℕ) : ℕ :=
  (v.keyAt word node arg).elim 0 (v.leastSlot word)

/-- Page zero returns the previous fields, including the genuine signed-cable
chunk. Page one returns the non-cable/header/range summand of the merge. -/
def decodeDigit (word : Cell v.siteWord) (stage : Fin 2) (f : Fin 7)
    (arg : Fin v.args) (node : Fin v.nodes) : Cell v.bits :=
  let prior:=v.rawField word node.val arg.val f
  let tag:=v.rawField word node.val arg.val 0
  if stage.val=0 ∨ 4≤f.val ∨ tag.val=2 then prior
  else if f.val=2 ∧ tag.val=0 then (v.localName word node.val arg.val:Cell v.bits) else 0

/-- On the second pass only a pin can retain its original kind. -/
theorem decode_kept_tag_le (word : Cell v.siteWord) (arg : Fin v.args) (node : Fin v.nodes) :
    (v.decodeDigit word 1 0 arg node).val ≤ 2 := by
  by_cases pin : (v.rawField word node.val arg.val 0).val = 2
  · simp [decodeDigit,pin]
  · simp [decodeDigit,pin]

theorem owns_unique (word : Cell v.siteWord) (n : ℕ) {i j : Fin v.donors}
    (a : v.owns word n i) (b : v.owns word n j) : i=j :=by
  rcases lt_trichotomy i.val j.val with lt|eqn|gt
  · have dis:=ProtocolRAMPortRanks.prefix_disjoint (v.originalCount word) Fin.val lt
    change v.offset word i+v.originalCount word i≤v.offset word j at dis
    dsimp only [owns] at a b;omega
  · exact Fin.ext eqn
  · have dis:=ProtocolRAMPortRanks.prefix_disjoint (v.originalCount word) Fin.val gt
    change v.offset word j+v.originalCount word j≤v.offset word i at dis
    dsimp only [owns] at a b;omega

theorem root_at (word : Cell v.siteWord) (q : Fin v.donors) (n : ℕ)
    (occupied : n<v.originalCount word q) : v.root word (v.offset word q+n)=some q :=by
  have hit : v.owns word (v.offset word q+n) q:=⟨Nat.le_add_right ..,Nat.add_lt_add_left occupied _⟩
  cases eqn:v.root word (v.offset word q+n) with
  | none=>
    have absent:=List.find?_eq_none.mp eqn q (List.mem_finRange q)
    exact False.elim (absent (decide_eq_true hit))
  | some z=>
    have found:=List.find?_some eqn
    have eq:=v.owns_unique word _ (of_decide_eq_true found) hit
    rw [eq]

def donorDigit (word : Cell v.siteWord) (node : ℕ) : Cell v.bits :=
  ((v.root word node).elim 0 (fun d=>d.val+1):ℕ)

theorem donor_read (word : Cell v.siteWord) (q : Fin v.donors) (n : ℕ)
    (occupied : n<v.originalCount word q) (room : v.donors<2^v.bits) :
    (v.donorDigit word (v.offset word q+n)).val=q.val+1 :=by
  simp only [donorDigit,v.root_at word q n occupied,Option.elim_some,Fin.val_cast_of_lt ((Nat.succ_le_of_lt q.isLt).trans_lt room)]

theorem location_read (word : Cell v.siteWord) (q : Fin v.donors) (n : Fin v.previousNodes) (j : Fin v.previousArgs)
    (live : n.val<v.originalCount word q) (present : j.val<(v.entry word q n v.arityField).val) :
    v.location word (v.offset word q+n.val) j.val=some (q,n,j) :=by
  simp [location,v.root_at word q n.val live,n.isLt,j.isLt,present]

theorem cell_read (word : Cell v.siteWord) (q : Fin v.donors) (n : Fin v.previousNodes) (j : Fin v.previousArgs) (f : Fin 7)
    (live : n.val<v.originalCount word q) (present : j.val<(v.entry word q n v.arityField).val) :
    v.rawField word (v.offset word q+n.val) j.val f=v.entry word q n (v.operandField f j) :=by
  simp [rawField,v.location_read word q n j live present]

theorem ghost (word : Cell v.siteWord) (node arg : ℕ) (absent : v.location word node arg=none) :
    (∀f,v.rawField word node arg f=0) ∧ v.keyAt word node arg=none ∧ v.localName word node arg=0 := by
  simp [rawField,keyAt,localName,absent]

theorem entry_zero (q : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) : v.entry 0 q n f=0 :=by
  change ScalarOperand.take (a:=v.bits) q (ScalarOperand.take (a:=v.stripWord) (finProdFinEquiv (f,n) : Fin v.channels) 0)=0
  rw [ScalarOperand.take_zero]
  exact ScalarOperand.take_zero (a:=v.bits) q

theorem root_zero (n : ℕ) : v.root 0 n=none :=by
  unfold root
  apply List.find?_eq_none.mpr
  intro d _
  have empty : v.originalCount 0 d=0:=by simp [originalCount,v.entry_zero]
  simp [owns,empty]

theorem decode_zero (r : Fin 2) (f : Fin 7) (arg : Fin v.args) (n : Fin v.nodes) :
    v.decodeDigit 0 r f arg n=0 :=by
  have no : v.location 0 n.val arg.val=none:=by simp [location,v.root_zero]
  obtain ⟨raw,_,key⟩:=v.ghost 0 n.val arg.val no
  simp [decodeDigit,raw,key]

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
