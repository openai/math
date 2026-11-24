import OAI.Computability.VPVNP.LiveProgramSchedule
import OAI.Computability.VPVNP.LiveHeaderProtected
import OAI.Computability.VPVNP.LiveHeaderOutputFrame
import OAI.Computability.VPVNP.LiveHeaderModeReject
import OAI.Computability.VPVNP.LiveHeaderPaddingReject
import OAI.Computability.VPVNP.LiveDeterministicPaths

/-!
# Entering and leaving the header stage of the full live program

The physical machine reads the outer tag at the first address beyond its
processor array. Its header stage reserves the next address for its own
dispatcher. Every header call protects the outer tag. The accepting call
updates that tag to the mode router and resets the cursor to zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Header

open BurstRAM BurstRAM.PrivateRAM LiveHeaderProgram LiveHeaderSchedule LiveHeader ChainAssignments

/-- The concrete live header lengths obtained by evaluating the fixed size expressions at the
group geometry. -/
def sizes (c : Constants) (g : Geometry) := c.lengths.eval g
/-- Base of the header workspace, one word beyond the outer stage tag that follows the
processor array. -/
def base (g : Geometry) := 2^g.d+1
/-- Word address of the outer stage tag checked and updated by the linked header program. -/
abbrev addr (g : Geometry) (lit : LiteralPrefix) := Pieces.word g lit (.geometry Layout.stageTag)
private abbrev tables (c : Constants) (p : UniversalMachine.Program) (O : PairTable) := Pieces.table (rows c p O)
private abbrev words (c : Constants) (p : UniversalMachine.Program) (O : PairTable) (g : Geometry) (lit : LiteralPrefix) :=
  Pieces.word g lit ∘ Pieces.bank (rows c p O)

private theorem relocated_call (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (fuel : ℕ) (st : Word g.w) (m : Memory g.w) (bits : List Bool) :
    let T := ((tables c p O Stage.header).instantiate g.w (words c p O g lit)).program
    let P := (LiveHeaderProgram.program.instantiate g.w (LiveHeaderProgram.publicData g.w (sizes c g) (base g))).program
    execute T fuel (T.start st) m bits = execute P fuel (P.start st) m bits := by
  dsimp only
  rw [Pieces.component_eq]
  let ops := fun j => Fin.ofNat (2^g.w) ((HeaderLayout.operands c.lengths Layout.header j).eval g)
  have h : ops = LiveHeaderProgram.publicData g.w (sizes c g) (base g) := funext (HeaderLayout.operands_eq g c.lengths Layout.header)
  change execute (LiveHeaderProgram.program.instantiate g.w ops).program fuel ((LiveHeaderProgram.program.instantiate g.w ops).program.start st) m bits = _
  rw [h]

private theorem segment_eq {w : ℕ} {C D : Type*} (T : BurstRAM.Program w C) (P : BurstRAM.Program w D)
    (fuel : ℕ) (h : ∀ st mem b, execute T fuel (T.start st) mem b = execute P fuel (P.start st) mem b)
    (st : Option (Word w)) (m : Memory w) (bs : List (List Bool)) :
    runSegment T fuel st m bs = runSegment P fuel st m bs := by
  induction bs generalizing st m with
  | nil => rfl
  | cons b bs ih =>
    cases st with
    | none => rfl
    | some st =>
      simp only [runSegment,h]
      cases execute P fuel (P.start st) m b <;> simp only [ih]

private theorem relocated_segment (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (fuel : ℕ) (st : Option (Word g.w)) (m : Memory g.w) (bs : List (List Bool)) :
    let T := ((tables c p O Stage.header).instantiate g.w (words c p O g lit)).program
    let P := (LiveHeaderProgram.program.instantiate g.w (LiveHeaderProgram.publicData g.w (sizes c g) (base g))).program
    runSegment T fuel st m bs = runSegment P fuel st m bs :=
  segment_eq _ _ fuel (relocated_call c p O g lit fuel) st m bs

theorem addr_value (g : Geometry) (lit : LiteralPrefix) (c : Constants) (hfit : limit (sizes c g) (base g) ≤ 2^g.w) :
    (addr g lit).val = 2^g.d := by
  change 2^g.d % (2^g.w) = _
  apply Nat.mod_eq_of_lt
  rw [limit_eq] at hfit
  unfold base at hfit
  omega

private theorem outer_program (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) :
    (LiveProgram.machine c p O g lit).program =
      (LiveStageLink.machine (tables c p O) (LiveProgram.next p) (words c p O g lit) (addr g lit)).program := by
  unfold LiveProgram.machine Pieces.machine Pieces.program
  rw [Pieces.data_eq]
  rfl

/-- Every continuing source call of the physical header leaves the outer
stage tag intact, for arbitrary processor and scratch contents. -/
theorem tagFrame (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (fuel : ℕ) (hw : 4 ≤ g.w) (fit : limit (sizes c g) (base g) ≤ 2^g.w)
    (ht : stages.length ≤ 2^g.w) :
    LiveStageLink.TagFrame (tables c p O) (words c p O g lit) (addr g lit) Stage.header fuel (fun _ _ => True) := by
  intro st m bits rep st' _ htag hc _
  rw [relocated_call] at hc
  have ha : (addr g lit).val < base g := by rw [addr_value g lit c fit]; exact Nat.lt_succ_self _
  exact ⟨trivial,(native_protected (sizes c g) (base g) fit hw ht fuel st m bits rep hc _ ha).trans htag⟩

private theorem segment_frame {w : ℕ} {C : Type*} (P : BurstRAM.Program w C) (fuel : ℕ) (a : Word w)
    (frame : ∀ st m b r, execute P fuel (P.start st) m b = some r → after m r.events a.val = m a.val)
    {st : Option (Word w)} {m : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (hr : runSegment P fuel st m bs = some rs) : LiveStageLink.PreservesTagOnReturns a m rs := by
  induction bs generalizing st m rs with
  | nil => simp [runSegment] at hr; subst rs; trivial
  | cons b bs ih =>
    cases st with
    | none => simp [runSegment] at hr
    | some st =>
      simp only [runSegment] at hr
      cases hc : execute P fuel (P.start st) m b with
      | none => simp [hc] at hr
      | some r =>
        simp only [hc,Option.map_eq_some_iff] at hr
        obtain ⟨rest,hrest,rfl⟩ := hr
        exact ⟨fun _ => frame st m b r hc,ih hrest⟩

set_option maxHeartbeats 1500000 in
/-- The actual linked live program reaches its mode router on exactly the
deterministic header choices. The transferred memory still has the complete
header output image, and the cost includes both dispatchers. -/
theorem valid_prefix (c : Constants) (p : UniversalMachine.Program) (O : PairTable) (g : Geometry)
    (lit : LiteralPrefix) (fuel : ℕ) (hw : 4 ≤ g.w) (advice : CutSchedule.Bits (sizes c g).advice)
    (cuts : AllCuts (sizes c g).h (sizes c g).delta) (i : Fin (2^((sizes c g).h+1))) (tag : Mode.Tag)
    (bounds : Fields.Bounds (sizes c g) (base g) g.d g.w) (hi : (sizes c g).h+2 ≤ 2^g.d)
    (had : (sizes c g).advice ≤ 2^g.d) (ht : stages.length ≤ 2^g.w) (hcap : 154 ≤ fuel)
    (mode : physicalTag cuts i = some tag) (pad : ∀ side, Fields.ValidPadding (sizes c g) cuts i tag side) :
    let m := physicalMemory (d := g.d) hw advice cuts i
    ∃ rs, runSegment (LiveProgram.machine c p O g lit).program fuel (some 0) m (List.replicate (callBound (sizes c g)) []) = some rs ∧
      endState (some 0) rs = some 0 ∧ Output (sizes c g) (base g) g.d hw advice cuts i tag (after m (eventLog rs)) ∧
      after m (eventLog rs) (addr g lit).val = LiveStageLink.tagWord g.w Stage.mode ∧
      rs.length = callBound (sizes c g) ∧ RAMBuckets.cost Report.probes rs ≤ costBound (sizes c g) ∧
      ∀ r ∈ rs, r.probes ≤ 10 := by
  let s := sizes c g
  let m := physicalMemory (d := g.d) hw advice cuts i
  obtain ⟨raw,hr,he,image,len,budget,probes,_⟩ := valid_native s (base g) 107 hw advice cuts i tag bounds hi had ht le_rfl mode pad
  have av := addr_value g lit c bounds.fit.le
  have below : (addr g lit).val < base g := by rw [av]; exact Nat.lt_succ_self _
  have hz : m (addr g lit).val = LiveStageLink.tagWord g.w Stage.header := by
    simp [m,physicalMemory,RAMMemory.initialMemory,av,LiveStageLink.tagWord,Stage.header]
  have hr' := (relocated_segment c p O g lit 107 (some 0) m _).trans hr
  let T := ((tables c p O Stage.header).instantiate g.w (words c p O g lit)).program
  have frame := segment_frame T 107 (addr g lit) (fun st mem b r h => native_protected s (base g) bounds.fit.le hw ht
    107 st mem b r ((relocated_call c p O g lit 107 st mem b).symm.trans h) _ below) hr'
  have fit21 : 21 ≤ 2^g.w := (by decide : 21 ≤ stages.length).trans ht
  obtain ⟨hrun,hstate,hm,hcost⟩ := LiveStageLink.runSegment_accepting (tables c p O) (LiveProgram.next p) (words c p O g lit)
    (addr g lit) Stage.header fit21 (by omega : 107+2*21+5 ≤ fuel) 0 m _ raw hz frame hr' he
  let logs := raw.map (LiveStageLink.linkedReport (LiveProgram.next p) (addr g lit) Stage.header)
  have hn : LiveProgram.next p Stage.header = some Stage.mode := rfl
  rw [hn] at hm hcost hstate
  have hmem : after m (eventLog logs) = writeMemory (after m (eventLog raw)) (addr g lit) (LiveStageLink.tagWord g.w Stage.mode) := hm
  refine ⟨logs, ?_, hstate, ?_, ?_, ?_, ?_, ?_⟩
  · rw [outer_program]; exact hrun
  · rw [hmem]; exact image.write_outer _ _ av.ge below
  · rw [hmem]; simp [writeMemory]
  · simpa [logs] using len
  · change RAMBuckets.cost Report.probes logs ≤ costBound s
    have hx : RAMBuckets.cost Report.probes logs = RAMBuckets.cost Report.probes raw + raw.length + 1 := hcost
    rw [hx]
    have hp : 0 < raw.length := by rw [len]; unfold callBound; omega
    omega
  · intro r h
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    rw [LiveStageLink.linkedReport_probes]
    have hp := probes u hu
    split <;> omega

set_option maxHeartbeats 1000000 in
/-- Any accepted path of the full live program must first accept the physical
header checks at its actual remaining source cap. -/
theorem necessary (c : Constants) (p : UniversalMachine.Program) (O : PairTable) (g : Geometry)
    (lit : LiteralPrefix) (fuel : ℕ) (hw : 4 ≤ g.w) (advice : CutSchedule.Bits (sizes c g).advice)
    (cuts : AllCuts (sizes c g).h (sizes c g).delta) (i : Fin (2^((sizes c g).h+1)))
    (bounds : Fields.Bounds (sizes c g) (base g) g.d g.w) (hi : (sizes c g).h+2 ≤ 2^g.d)
    (had : (sizes c g).advice ≤ 2^g.d) (ht : stages.length ≤ 2^g.w) (hcap : 154 ≤ fuel)
    (bs : List (List Bool)) (logs : List (Report g.w))
    (run : runSegment (LiveProgram.machine c p O g lit).program fuel (some 0)
      (physicalMemory (d := g.d) hw advice cuts i) bs = some logs)
    (halt : endState (some 0) logs = none) :
    ∃ tag, physicalTag cuts i = some tag ∧ ∀ side, Fields.ValidPadding (sizes c g) cuts i tag side := by
  let s := sizes c g
  let m := physicalMemory (d := g.d) hw advice cuts i
  let a := addr g lit
  have av := addr_value g lit c bounds.fit.le
  have below : a.val < base g := by change (addr g lit).val < _; rw [av]; exact Nat.lt_succ_self _
  have hz : m a.val = LiveStageLink.tagWord g.w Stage.header := by
    simp [a,m,physicalMemory,RAMMemory.initialMemory,av,LiveStageLink.tagWord,Stage.header]
  have fit21 : 21 ≤ 2^g.w := (by decide : 21 ≤ stages.length).trans ht
  rw [outer_program] at run
  obtain ⟨before,_,raw,_,source,stop⟩ := LiveStageLink.recover_accepting_stage
    (tables c p O) (LiveProgram.next p) (words c p O g lit) a Stage.header fit21
    (by omega : 2*21+2 ≤ fuel) 0 m bs logs hz (by
      intro st mem bits rep he _
      have hs := (relocated_call c p O g lit _ st mem bits).symm.trans he
      exact native_protected s (base g) bounds.fit.le hw ht _ st mem bits rep hs _ below) run halt
  rw [relocated_segment] at source
  let cap := fuel-(LiveStageLink.dispatchEvents a Stage.header).length
  have disp : (LiveStageLink.dispatchEvents a Stage.header).length = 4 := rfl
  have capFit : 107 ≤ cap := by dsimp only [cap]; rw [disp]; omega
  cases tagEq : physicalTag cuts i with
  | none =>
    exact (bad_mode_native s (base g) cap hw advice cuts i tagEq hi had bounds.scratch bounds.fit.le ht capFit
      ⟨before,raw,source,stop⟩).elim
  | some tag =>
    refine ⟨tag,rfl,?_⟩
    by_contra bad
    exact bad_padding_native s (base g) cap hw advice cuts i tag bounds hi had ht capFit tagEq bad
      ⟨before,raw,source,stop⟩

end LiveProgram.Header

end VPVNP
end Computability
end OAI
