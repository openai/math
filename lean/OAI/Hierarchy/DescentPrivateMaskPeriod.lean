import OAI.Hierarchy.DescentPrivateMaskDeck
import OAI.Hierarchy.DescentContactPostTrunkPitch
import OAI.Hierarchy.DescentResetCompactedCandidates

namespace OAI
/-! # Executing the private fields on the actual issued root pages and the retained pitch table -/
namespace Hierarchy.DescentPrivateMaskDeck.Shape
open DescentSIMDLookup DescentPackedZip DescentResetLocalRoster DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (A : DescentPrivateMaskDeck.Shape) (base : ℕ)
abbrev RootPages := Bool→Root A.residual A.ports→Bank
variable (pitch : DescentContactPreROM.Layout) (pages : A.RootPages)
local notation "N" => A.fields
local notation "H" => A.oldHosts*A.shapes
local notation "begin₀" => A.projected base
local notation "end₀" => A.endAddress base

/-- This decoder is part of the public schedule. Empty short IDs have a fixed zero operand. -/
def incoming (q : Fin A.keys) (j : Fin 3) : Expr :=
  if hit : ∃p,localPrivateId A.residual A.ports A.cap p=q then
    let t:=hit.choose
    pitch.priorView (A.query base t.2.2 j (.lookup (pages t.1 t.2.1) .row))
  else .lit 0

def fieldTerm (i : Fin N) : Expr :=
  let q : Fin A.keys×Fin 3:=finProdFinEquiv.symm i
  A.incoming base pitch pages q.1 q.2

def output (q : Fin A.keys) (j : Fin 3) (x : Fin A.blocks) : Bank :=
  DescentResetStemProject.bank begin₀ N H A.groups A.blocks A.metaBits A.oldBatch A.batch (finProdFinEquiv (q,j)) x

def operand (q : Fin A.keys) (j : Fin 3) (x : Fin A.blocks) := Expr.lookup (A.output base q j x) .row

def code (w : ℕ) := (A.wordsPhase w base).program.seq
  (DescentResetStemProjectExpr.program begin₀ H A.groups A.blocks A.metaBits A.oldBatch A.batch (A.fieldTerm base pitch pages) w)

def final {w : ℕ} (m : Memory w) :=
  DescentResetStemProjectExpr.image begin₀ H A.groups A.blocks A.metaBits A.oldBatch A.batch
    (A.fieldTerm base pitch pages) ((A.wordsPhase w base).image m)

def ticks := (4+10*A.count)+DescentResetStemProjectExpr.ticks begin₀ H A.groups A.blocks
  A.metaBits A.oldBatch A.batch (A.fieldTerm base pitch pages)

theorem any {w : ℕ} (m : Memory w) (batch : 0<A.batch) (blocks : 0<A.blocks)
    (fits : ∀q,(A.fieldTerm base pitch pages q).Fits w begin₀) (roof : end₀<2^w) :
    (A.code base pitch pages w).Exec m (A.final base pitch pages m) (A.ticks base pitch pages) ∧
    CheapCode (A.code base pitch pages w) ∧ ∀z,z<base ∨ end₀≤z→A.final base pitch pages m z=m z := by
  have cuts:=A.cuts base
  have first:=A.words_any base m (cuts.2.trans_lt roof)
  have later:=DescentResetStemProjectExpr.any begin₀ H A.groups A.blocks A.metaBits A.oldBatch A.batch
    (A.fieldTerm base pitch pages) ((A.wordsPhase w base).image m) batch blocks fits roof
  exact ⟨Procedure.Exec.then first.1 later.1,cheap_seq (A.wordsPhase w base).cheap later.2.2,fun z h=>
    (later.2.1 z (h.imp (fun low=>low.trans_le cuts.1) id)).trans
      (first.2 z (h.imp id (fun high=>cuts.2.trans high)))⟩

def phase {w : ℕ} (batch : 0<A.batch) (blocks : 0<A.blocks)
    (fits : ∀q,(A.fieldTerm base pitch pages q).Fits w begin₀) (roof : end₀<2^w) : NativePhase w :=
  ⟨A.code base pitch pages w,A.ticks base pitch pages,A.final base pitch pages,
    (A.any base pitch pages (fun _=>0) batch blocks fits roof).2.1⟩

theorem incoming_true (s : Bool) (t : Root A.residual A.ports) (l : Fin A.cap) (j : Fin 3) :
    A.incoming base pitch pages (localPrivateId A.residual A.ports A.cap (s,t,l)) j=
    pitch.priorView (A.query base l j (.lookup (pages s t) .row)) := by
  unfold incoming
  split
  · rename_i found
    rw [(localPrivateId A.residual A.ports A.cap).injective found.choose_spec]
  · rename_i missing
    exact (missing ⟨_, rfl⟩).elim

/-- The root pages are original reads. The pitch table is the earlier, immutable address map. -/
theorem incoming_fits {w : ℕ} (recorded : ∀s t,(pages s t).Fits w base)
    (before : pitch.markerBase≤base) (roof : begin₀<2^w) (i : Fin N) :
    (A.fieldTerm base pitch pages i).Fits w begin₀:=by
  unfold fieldTerm incoming
  dsimp only
  split
  · refine pitch.late_view_fits begin₀ (before.trans (A.cuts base).1)
      ((before.trans (A.cuts base).1).trans_lt roof) _ (A.query_fits base _ _ _ ?_ roof)
    exact ProtocolRAMGeneratedWrite.fits_mono _ (A.cuts base).1 ⟨recorded _ _,trivial⟩
  · trivial

/-- The original coarse-lane values extracted from the selected five-digit private row. -/
def measured (raw : Bool→Root A.residual A.ports→Fin pitch.hosts→Fin pitch.groups→Cell A.panels)
    (q : Fin A.keys) (j : Fin 3) (v : Fin (pitch.hosts*pitch.shapes)) (g : Fin pitch.groups) : Cell A.metaBits :=
  if hit : ∃p,localPrivateId A.residual A.ports A.cap p=q then
    let t:=hit.choose
    A.scalar t.2.2 j (raw t.1 t.2.1 (DescentContactProbePitch.owner v) g)
  else 0

theorem measured_true
    (raw : Bool→Root A.residual A.ports→Fin pitch.hosts→Fin pitch.groups→Cell A.panels)
    (s : Bool) (t : Root A.residual A.ports) (slot : Fin A.cap) (j : Fin 3) (v g) :
    A.measured pitch raw (localPrivateId A.residual A.ports A.cap (s,t,slot)) j v g=
      A.scalar slot j (raw s t (DescentContactProbePitch.owner v) g) :=by
  unfold measured
  split
  · rename_i found
    rw [(localPrivateId A.residual A.ports A.cap).injective found.choose_spec]
  · rename_i missing
    exact (missing ⟨_, rfl⟩).elim

theorem measured_source {w k : ℕ} (board : NonlinearExpanders.Graph pitch.n k)
    (reads : Fin pitch.oldFields→Expr) (prior : Bool→Fin pitch.half→Fin 5→Expr)
    (space : pitch.Space reads prior w) (initial m : Memory w)
    (held : ∀z,z<pitch.markerBase→m z=pitch.memory board reads prior space initial z)
    (earlier : pitch.markerBase≤base) (batch : A.oldBatch=pitch.batch)
    (recorded : ∀s t,(pages s t).Fits w base) (roof : begin₀<2^w)
    (raw : Bool→Root A.residual A.ports→Fin pitch.hosts→Fin pitch.groups→Cell A.panels)
    (stored : ∀s t,Source (.lookup (pages s t) .row) (raw s t) A.oldBatch m) (q : Fin A.keys) (f : Fin 3) :
    Source (A.incoming base pitch pages q f) (A.measured pitch raw q f) A.oldBatch ((A.wordsPhase w base).image m) :=by
  let after:=(A.wordsPhase w base).image m
  have kept (z) (hz:z<pitch.markerBase) : after z=pitch.memory board reads prior space initial z:=
    ((A.words_any base m roof).2 z (.inl (hz.trans_le earlier))).trans (held z hz)
  by_cases h:∃p,localPrivateId A.residual A.ports A.cap p=q
  · obtain ⟨⟨s,t,slot⟩, rfl⟩ := h
    rw [A.incoming_true]
    let vals : Fin pitch.hosts → Fin pitch.groups → Cell A.metaBits :=
      fun v g => A.scalar slot f (raw s t v g)
    have value : A.measured pitch raw (localPrivateId A.residual A.ports A.cap (s,t,slot)) f =
        DescentContactProbePitch.lift (S:=pitch.shapes) vals := by
      funext v g
      exact A.measured_true pitch raw s t slot f v g
    rw [value]
    let term := A.query base slot f (.lookup (pages s t) .row)
    have orig : Source term vals A.oldBatch after :=
      A.query_source base slot f (.lookup (pages s t) .row) (raw s t) m
        ⟨recorded _ _,trivial⟩ (stored _ _) roof
    rw [batch] at orig ⊢
    exact pitch.post_view board reads prior space initial after kept term vals orig
  · have empty : A.measured pitch raw q f = fun _ _ => 0 := by
      funext v g
      simp only [measured, dite_eq_right h]
    rw [empty]
    simp only [incoming, dite_eq_right h]
    intro p
    change 0=(((finFunctionFinEquiv (fun i : Fin A.oldBatch=>if _ : p.2.val*A.oldBatch+i.val<pitch.groups then
      (0:Cell A.metaBits) else 0)).val:ℕ):Word w)
    simp

theorem output_fits {w : ℕ} (q : Fin A.keys) (j : Fin 3) (x : Fin A.blocks) (roof : end₀<2^w) :
    (A.operand base q j x).Fits w end₀:=⟨DescentResetStemProject.page_fits _ _ roof,trivial⟩

/-- Gather the old coarse lane for the new group and its local block. -/
theorem projected_fields {w : ℕ} (m : Memory w) (oldPos : 0<A.oldBatch) (batch : 0<A.batch) (blocks : 0<A.blocks)
    (fits : ∀q,(A.fieldTerm base pitch pages q).Fits w begin₀) (roof : end₀<2^w)
    (values : Fin A.keys→Fin 3→Fin H→Fin (A.groups*A.blocks)→Cell A.metaBits)
    (actual : ∀q j,Source (A.incoming base pitch pages q j) (values q j) A.oldBatch ((A.wordsPhase w base).image m))
    (q : Fin A.keys) (j : Fin 3) (x : Fin A.blocks) :
    Source (A.operand base q j x) (fun v g=>values q j v (finProdFinEquiv (g,x))) A.batch (A.final base pitch pages m) := by
  let Y (i : Fin N) :=let t:Fin A.keys×Fin 3:=finProdFinEquiv.symm i; values t.1 t.2
  have src (i : Fin N) : Source (A.fieldTerm base pitch pages i) (Y i) A.oldBatch ((A.wordsPhase w base).image m):=actual _ _
  have done:=DescentResetStemProjectExpr.run begin₀ H A.groups A.blocks A.metaBits A.oldBatch A.batch
    (A.fieldTerm base pitch pages) ((A.wordsPhase w base).image m) Y oldPos batch blocks fits src roof
  simpa only [operand,output,final,Y,Equiv.symm_apply_apply] using done.2.1 (finProdFinEquiv (q,j)) x

private theorem source_reindex {b m₀ h h' g g' w : ℕ} {e : Expr} {mem : Memory w}
    {values : Fin h'→Fin g'→Cell b} (hosts : h=h') (groups : g=g')
    (read : Source e values m₀ mem) :
    Source e (fun v j=>values (v.cast hosts) (j.cast groups)) m₀ mem:=by
  subst h'
  subst g'
  exact read

/-- Read the final three native columns directly from the previously mounted root pages.
The two transports use the literal row-major old host and successor group/block packing. -/
theorem projected_original {w k : ℕ} (board : NonlinearExpanders.Graph pitch.n k)
    (reads : Fin pitch.oldFields→Expr) (prior : Bool→Fin pitch.half→Fin 5→Expr)
    (space : pitch.Space reads prior w) (initial m : Memory w)
    (held : ∀z,z<pitch.markerBase→m z=pitch.memory board reads prior space initial z)
    (earlier : pitch.markerBase≤base) (batchEq : A.oldBatch=pitch.batch)
    (hostEq : H=pitch.hosts*pitch.shapes) (laneEq : A.groups*A.blocks=pitch.groups)
    (recorded : ∀s t,(pages s t).Fits w base)
    (oldPos : 0<A.oldBatch) (batch : 0<A.batch) (blocks : 0<A.blocks) (roof : end₀<2^w)
    (raw : Bool→Root A.residual A.ports→Fin pitch.hosts→Fin pitch.groups→Cell A.panels)
    (stored : ∀s t,Source (.lookup (pages s t) .row) (raw s t) A.oldBatch m)
    (q : Fin A.keys) (j : Fin 3) (x : Fin A.blocks) :
    Source (A.operand base q j x) (fun v g=>
      A.measured pitch raw q j (v.cast hostEq) ((finProdFinEquiv (g,x)).cast laneEq))
      A.batch (A.final base pitch pages m):= by
  let V q j (v : Fin H) (g : Fin (A.groups*A.blocks)):=
    A.measured pitch raw q j (v.cast hostEq) (g.cast laneEq)
  have fit:=A.incoming_fits base pitch pages recorded earlier ((A.cuts base).2.trans_lt roof)
  apply A.projected_fields base pitch pages m oldPos batch blocks fit roof V _ q j x
  intro t f
  have fromPages:=A.measured_source base pitch pages board reads prior space initial m held earlier batchEq
    recorded ((A.cuts base).2.trans_lt roof) raw stored t f
  exact source_reindex hostEq laneEq fromPages


end
end Hierarchy.DescentPrivateMaskDeck.Shape

end OAI
