import OAI.Computability.BorderVNP.PackedBankHookWordRoom
import OAI.Computability.BorderVNP.PackedFrozenCompiledInner
import OAI.Computability.BorderVNP.PackedInheritedWorkSelected

/-! # Reading the selected outer history's complete executable site programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.Inherited.WorkWords Packing.PhysicalEpochs FrozenTape EnrichedOuter
open InheritedBank VPVNP.VerifierNetwork
open private transferChoice from OAI.Computability.BorderVNP.PackedInheritedWorkCompiledTree
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}

local notation3 "admitted" => Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
    (shape := boundaryShape S start) (w := w) budget)

/-- The complete state read at one attained physical boundary. Its saved width columns and
immutable rows describe the same executable program at the same physical site. -/
structure TapeReads (base : Format) {t : ℕ} (a : admitted t) (p : Site.Programs a.val.pack.layout)
    (y : ProgramSchemas.outerPins S start w base t → Bool) : Prop where
  widths : Boundary.WidthReads a.val p (y ∘ Sum.inl)
  tape : (ProgramSchemas.epoch S start w base t).schema.Image (y ∘ Sum.inr)
    (a.val.rows.site.trans Fin.valEmbedding) (fun v => (p v).program)

variable (C : Compiled bits deep budget cap w) (base : Format) (t : ℕ) (ht : t<T)
local notation3 (prettyPrint := false) "A" => C.atLevel t ht
local notation3 "outer" => ProgramSchemas.outerPins S start w base

variable (c : Fin (fan S) → Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
    (shape := boundaryShape S start) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)
    (y : ProgramSchemas.stagePins S start w base t S.rounds → Bool)

/-- The minimizing post-frame returns the selected root's exact private program and numeric
owner keys through its port flattening and its boundary rectangle. -/
theorem tapePost_reads (rows : (A).epoch.F.SiteRows) (number : e.Entry → ℕ)
    (q : (A).epoch.F.Hist ((A).epoch.run c).flat)
    (child : ∀ i, Boundary.WidthReads (c i).val (old i) (fun j => x (i,.inl j)))
    (root : (A).RootWidthReads rows number c old q (y ∘ Sum.inl))
    (image : (ProgramSchemas.stage S start w base t S.rounds).schema.Image (y ∘ Sum.inr)
      ((((A).returned c).run.root q).val.names.sites.trans Fin.valEmbedding) (fun v => ((A).rootPrivate rows c old number q v).program)) :
    TapeReads base ((A).epoch.term c q) ((A).epoch.privatePrograms rows c old number q)
      ((C.tapePost base t ht).eval (Sum.elim x y)) := by
  let previous := fun z : Fin (fan S) × Boundary.OuterWidthPins S start (boundaryShape S start) w t => x (z.1,.inl z.2)
  have hw : (C.tapePost base t ht).eval (Sum.elim x y) ∘ Sum.inl =
      (A).widthPost.eval (Sum.elim previous (y ∘ Sum.inl)) := funext (ProgramSchemas.forwardRoot_post _ x y)
  constructor
  · rw [hw]
    constructor
    · funext j
      have oldWords : (fun z : Fin (fan S) × Boundary.Pins S start (boundaryShape S start) w t =>
          previous (z.1,.inl z.2)) = childWords c := funext fun z => congrFun (child z.1).geometry z.2
      change (A).widthPost.eval (Sum.elim previous (y ∘ Sum.inl)) (.inl j) =
        (A).post.eval (Sum.elim (childWords c) (((A).returned c).run.root q).val.words) j
      rw [(A).widthPost_geo,oldWords,root.geometry]
    · exact fun b => (A).widthPost_covers rows c old number q previous (y ∘ Sum.inl) b (root.covers b)
  · have tape : (C.tapePost base t ht).eval (Sum.elim x y) ∘ Sum.inr = y ∘ Sum.inr :=
      funext (ProgramSchemas.forwardRoot_tape _ x y)
    rw [tape]
    change (ProgramSchemas.stage S start w base t S.rounds).schema.Image (y ∘ Sum.inr)
      ((((A).returned c).rows q).site.trans Fin.valEmbedding) (fun v => ((A).rootPrivate rows c old number q v).program)
    rw [((A).returned c).rows_eq q]
    exact image

variable (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start)) (wr : WidthRanges S start T w) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ) (B : ℕ)
local notation3 (prettyPrint := false) "inv" => WidthInvariant (S := S) (bits := bits) (budget := budget)
  (start := start) (w := w) header leaf B
local notation3 (prettyPrint := false) "steps" => C.tapeSteps base header leaf wr hm
local notation3 (prettyPrint := false) "names" => C.privateSiteRows leaf seeds

variable {σ : Type} [Fintype σ] (f : Frame σ (ProgramSchemas.outerPins S start w base 0)) (input : σ → Bool)
    (seed : Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) 0) (initial : Site.Programs seed.val.pack.layout)
    (small : (PortTable.mk _ leaf header).Widths bits w) (room : 2*(S.publicProgramFactor^T*B) < 2^w)
    (hook : HookRoom S T w B) (basePorts : header.Reads seed.val.pack.layout seed.val.rows.site leaf)
    (baseCap : SiteCap seed.val.route initial.bankFields true B) (startRead : TapeReads base seed initial (f.eval input))

include small room hook basePorts baseCap startRead in
/-- Every native history reads its full executable program at the physical owner row,
including the returned geometry, both width columns and the ordered frozen records. -/
theorem tape_pack_read (n : ℕ) (hn : n≤T) (q : (packHistory seed C.machine.epoch n).Index) :
    TapeReads base ((packHistory seed C.machine.epoch n).term q)
      (C.machine.historyPrivatePrograms names number seed initial n hn q)
      (output steps n hn (repeatLeaf (fan S) f n) input (C.machine.packBits seed n hn q)) := by
  let read t (a : admitted t) (pr : Site.Programs a.val.pack.layout) (z : outer t → Bool) :=
    inv t a pr ∧ TapeReads base a pr z
  have bottom : read 0 seed initial (f.eval input) :=
    ⟨⟨basePorts,by simpa only [pow_zero,one_mul] using baseCap⟩,startRead⟩
  apply (C.machine.private_pack_output seed steps names number read f input initial bottom ?_ n hn q).2
  intro t ht c programs y child
  let E := C.machine t ht
  let x := fun z : Fin (fan S) × outer t => y z.1 z.2
  let test (a : admitted (t+1)) (pr : Site.Programs a.val.pack.layout)
      (g : Machine.Guess S start (fun _ _ => w) t → Bool) :=
    read (t+1) a pr (fun j => (steps t ht).eval (Sum.elim x g) (.inl j))
  have localRead (j : E.F.Hist (E.run c).flat) :
      test (E.term c j) (E.privatePrograms (names t ht) c programs number j) ((E.run c).word E.room j) := by
    let epochCompilation := C.atLevel t ht
    let mass := S.publicProgramFactor^t*B
    let bound := widthBudget S mass
    have caps (i) : SiteCap (c i).val.route (programs i).bankFields true mass := (child i).1.2
    have hmass : 0 < mass := (Nat.add_pos_left (by decide : 0<1) _).trans_le
      (caps ⟨0,pow_pos S.positiveFanIn _⟩ 1)
    have fits (i) (hi : i≤S.rounds) : 2*bound i < 2^w :=
      (Nat.mul_le_mul_left 2 (widthBudget_horizon S B ht hi)).trans_lt room
    have first := fits 0 (Nat.zero_le _)
    have one : 1 < 2^w := by
      have positive : 0<bound 0 := widthBudget_pos S hmass 0
      omega
    have leafFit : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
        Fin (hopCount S.budget S.radius)))*mass < 2^w := by
      simp only [bound,widthBudget,pow_zero,one_mul] at first
      omega
    have root := C.stage_root_read base t ht header leaf wr seeds c programs x mass hm number
      (fun i => (child i).2.widths) (fun i => (child i).2.tape) (fun i => (child i).1.1) small caps hmass
      leafFit one (fun i => fits _ i.isLt) (hook t ht) j
    let pre := C.tapePre base t ht (prepHeader t header) (wr.initial t ht)
    let nodes := C.stageSteps base header leaf wr hm t ht
    let guess := (E.run c).word E.room j
    let rootBits := fun z => (flatEpoch nodes).eval (Sum.elim (pre.eval x) guess) (.inl z)
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact epochCompilation.widthReturn_ports c j _ _ root.widths.ports
    · have next := E.privatePrograms_bankCap (names t ht) number c programs true mass caps j
      simpa only [mass,pow_succ',Nat.mul_assoc] using next
    · change TapeReads base (E.term c j) (E.privatePrograms (names t ht) c programs number j)
        (fun z => (wrappedEpoch pre nodes (C.tapePost base t ht)).eval (Sum.elim x guess) (.inl z))
      rw [wrappedEpoch_state]
      exact C.tapePost_reads base t ht c programs x rootBits (names t ht) number j
        (fun i => (child i).2.widths) ⟨root.widths.geometry,root.widths.widths⟩ root.tape
  have eqn : C.machine.epoch t c = E.choice c := dite_eq_left ht
  exact transferChoice (fun a : admitted (t+1) => Site.Programs a.val.pack.layout) test eqn
    (E.privatePrograms (names t ht) c programs number) ((E.run c).word E.room) localRead

include small room hook basePorts baseCap startRead in
/-- The flattened terminal directory on the actual chosen outer histogram reads the
complete private program of each terminal site and the zero widths of vacant rows. -/
theorem terminal_tape_read (q : (packHistory seed C.machine.epoch T).Index) :
    let a := ((packHistory seed C.machine.epoch T).term q).val
    let y := output steps T le_rfl (repeatLeaf (fan S) f T) input (C.machine.packBits seed T le_rfl q)
    let p := C.machine.terminalPrivatePrograms names number seed initial q
    (y ∘ Sum.inl) ∘ Sum.inl = a.words ∧
      (∀ b, Covers a.rows.flatten.site (fun v => if b then (p v).program.size else (p v).program.work)
        (assignedColumn b) (y ∘ Sum.inl)) ∧
      (ProgramSchemas.epoch S start w base T).schema.Image (y ∘ Sum.inr) (a.rows.flatten.site.trans Fin.valEmbedding)
        (fun v => (p v).program) := by
  have h := C.tape_pack_read base header leaf wr hm seeds number B f input seed initial small room hook
    basePorts baseCap startRead T le_rfl q
  exact ⟨h.widths.geometry,h.widths.covers,h.tape⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
