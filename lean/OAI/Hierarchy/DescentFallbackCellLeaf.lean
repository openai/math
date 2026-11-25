import OAI.Hierarchy.DescentFallbackSignedPeer
import OAI.Hierarchy.DescentPackedIssuedFallback
import OAI.Hierarchy.DescentIssuedTreeArrival

namespace OAI
/-! # Compact signed-port and measured-endpoint inputs to the fallback leaf renderer -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "H" => Host J V k
local notation "src" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "shortT" => fun t=>shortName c (T.code t)
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
set_option quotPrecheck false in
local notation "oldCell" => fun h : H=>(frame.host h.1.2,Fin.cast (congrArg (fun t=>2^t) frame.extent.symm) (oldBlock digits h))

/-- These two fields depend on one old host and transformed leaf only. -/
def fallbackCell (s : Bool) (u : H) := (R).fall s (oldCell u)
def exceptionalCell (u : H) : Bool := decide
  (baseOf (R).b (R).depth (R).L (oldCell u)∈validBases (R).b (R).keys ∨ (R).hub (oldCell u).1)

theorem cell_old (s : Bool) (e : E) : (R).old s e=oldCell (home A (src s e)) := by
  apply Prod.ext
  · cases s <;> exact frame.actor _ _
  · apply Fin.ext
    cases s <;> exact frame.oldBlock _ _

theorem cell_home (s : Bool) (e : E) : fallbackCell A S ready digits Z T frame s (home A (src s e))=T.home (src s e) := by
  rw [fallbackCell,←cell_old A S ready digits Z T frame]
  cases s <;> exact (T.attach _ _).symm

theorem cell_mode (s : Bool) (e : E) : ¬use e ↔
    exceptionalCell A S ready digits Z T frame (home A (src s e)) ||
      exceptionalCell A S ready digits Z T frame (home A (src (!s) e)) := by
  let marked (x : Z.V × Block Z.k) : Prop :=
    baseOf (R).b (R).depth (R).L x ∈ validBases (R).b (R).keys ∨ (R).hub x.1
  have flag (side : Bool) :
      exceptionalCell A S ready digits Z T frame (home A (src side e)) = true ↔
        marked ((R).old side e) := by
    have eqn := congrArg (fun x => decide (marked x)) (cell_old A S ready digits Z T frame side e)
    change decide (marked (oldCell (home A (src side e)))) = true ↔ _
    rw [←eqn]
    exact ⟨of_decide_eq_true,decide_eq_true⟩
  rw [Bool.or_eq_true, flag, flag]
  cases s <;> simp only [useRotor, Bool.forall_bool, Bool.not_true, Bool.not_false, marked] <;> tauto

include frame in
theorem fell_iff (s : Bool) (t : Z.Fallback) (e : E) :
    falls A S ready Z s t e ↔ ¬use e ∧ T.home (src s e)=t := by
  rw [←cell_home A S ready digits Z T frame s e,fallbackCell,←cell_old A S ready digits Z T frame]
  by_cases rotor : use e <;> cases s <;> simp [falls,Placement.contact,Placement.owner,contact,owner,pair,rotor]

include frame in
theorem opposite_attach (s : Bool) (t : Z.Fallback) (e : E) (yes : falls A S ready Z s t e) :
    opposite (R) s t ⟨(R).contact e,yes⟩=T.home (src (!s) e) := by
  rw [←cell_home A S ready digits Z T frame (!s) e,fallbackCell,←cell_old A S ready digits Z T frame]
  have off:=(fell_iff A S ready digits Z T frame s t e).mp yes |>.1
  cases s <;> simp [opposite,Placement.contact,contact,off,pair]

/-- Numeric leaf from the true measured window. Size and rank may be taken
from the shared compact per-host leaf dictionary. -/
def leafValue (t : Z.Fallback) (dest : Z.V×DescentContacts.Endpoint (2^Z.n)) : Fin (2^Ht) :=
  let window:=T.leaves.window (shortT t)
  let rank:=(Finset.univ.filter (fun y : ↥window=>endpoint T.columns.host y.val<endpoint T.columns.host dest)).card
  ⟨DescentIssuedTreeArrival.table Ht (window.card*2^Ht+rank)%2^Ht,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

include frame in
theorem leafValue_at (s : Bool) (t : Z.Fallback) (e : E) (yes : falls A S ready Z s t e) :
    some (leafValue A S ready Z T t (shortT (T.home (src (!s) e))))=arrivedLeaf A S ready Z T s t e := by
  let link : DescentRouterSlots.LinkId Z.placement.owner s (.inr t) := ⟨Z.placement.contact e,yes⟩
  let word := (Z.placement.fallbackBook s t).codes link
  let win := T.leaves.window (shortT t)
  let rank := (Finset.univ.filter (fun y : ↥win => endpoint T.columns.host y.val <
    endpoint T.columns.host (shortT (T.home (src (!s) e))))).card
  have num : (DescentRotor.bitWord _ word).val = rank := by
    simpa only [word,rank,win,link,opposite_attach A S ready digits Z T frame s t e yes] using
      T.leaves.digits s t link
  have leaf_lt : start Ht word < stop Ht word :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.two_pow_pos _)
  have room := leaf_lt.trans_le (stop_le (T.bookHeight s t) word)
  rw [arrivedLeaf,dite_eq_left yes]
  apply congrArg some
  apply Fin.ext
  change DescentIssuedTreeArrival.table Ht (win.card*2^Ht+rank)%2^Ht = start Ht word
  rw [←num,DescentIssuedTreeArrival.table_leaf win.card (T.leaves.depth s t) (T.bookHeight s t) word,
    Nat.mod_eq_of_lt room]

/-- Front and back data are read at actual old cell addresses. In particular
the second endpoint is selected by the compact neighbor field of the signed port. -/
def cellLeaf (s : Bool) (t : Z.Fallback) (u v : H) : Option (Fin (2^Ht)) :=
  if (exceptionalCell A S ready digits Z T frame u || exceptionalCell A S ready digits Z T frame v) &&
    decide (shortT (fallbackCell A S ready digits Z T frame s u)=shortT t) then
    some (leafValue A S ready Z T t (shortT (fallbackCell A S ready digits Z T frame (!s) v)))
  else none

theorem cellLeaf_read (s : Bool) (t : Z.Fallback) (e : E)
    (root : coarseName c (T.code (T.home (src s e)))=coarseName c (T.code t)) :
    cellLeaf A S ready digits Z T frame s t (home A (src s e)) (home A (src (!s) e))=
      arrivedLeaf A S ready Z T s t e := by
  have eqn : shortT (T.home (src s e))=shortT t ↔ T.home (src s e)=t :=
    ⟨fun h=>coarse_recover (n:=Z.n) (k:=Z.k) c T.code T.codeLegal root h,fun h=>congrArg shortT h⟩
  have gate : ((exceptionalCell A S ready digits Z T frame (home A (src s e)) ||
    exceptionalCell A S ready digits Z T frame (home A (src (!s) e))) &&
      decide (shortT (T.home (src s e))=shortT t))=true ↔ falls A S ready Z s t e := by
    rw [Bool.and_eq_true,decide_eq_true_eq,←cell_mode A S ready digits Z T frame,eqn, fell_iff A S ready digits Z T frame]
  simp only [cellLeaf,cell_home A S ready digits Z T frame]
  by_cases h : falls A S ready Z s t e
  · rw [ite_eq_left (gate.mpr h)]
    exact leafValue_at A S ready digits Z T frame s t e h
  · rw [ite_eq_right (fun hh=>h (gate.mp hh)),arrivedLeaf,dite_eq_right h]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
