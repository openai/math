import OAI.Computability.VPVNP.PairSimulationAssembly

/-!
# Binary size of the descriptor scans

At a shrinking level the motifs are a subset of the old actual arcs. At
a refresh level there is one motif per port block. Each consumes a fixed
number of checked coordinates whose bit length is logarithmic in the
largest incoming width. The estimates here sum the concrete selector
stream and the old site and slot lists along the actual execution branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords NetworkKernel
open scoped Classical

variable {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R}

/-- Extract the term-selector reader at each pass of an execution, following its selected
continuation to form the reader for a whole descriptor path. -/
def outerReaders {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → ChoiceReader.passReaders E
  | .done _, _, _ => ()
  | .more _ tail, W, r => ⟨r.1.select, fun i => outerReaders (tail i) (W.2 i) (r.2 i)⟩

/-- Number of old site records and outgoing-slot records scanned once, plus
the number of binary guesses made by the actual outer-term parser. -/
def scanUnits {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → E.Choices → ℕ
  | .done _, _, _, _ => 0
  | @StateExecution.more _ _ _ _ a _ _ _ X _ tail, W, r, z =>
    X.positions * (2 ^ a + 1) + (r.1.select.encode z.1).length + scanUnits (tail z.1) (W.2 z.1) (r.2 z.1) z.2

theorem outerBits_le_scanUnits {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses κ) (r : ExecutionReaders E W) (z : E.Choices) :
    ((ChoiceReader.execution E (outerReaders E W r)).encode z).length ≤ scanUnits E W r z := by
  induction E with
  | done => exact le_rfl
  | @more a g b' n' X p tail ih =>
    change (r.1.select.encode z.1 ++ _).length ≤ X.positions * (2 ^ a + 1) + _ + _
    rw [List.length_append]
    exact Nat.add_le_add (Nat.le_add_left _ _) (ih z.1 (W.2 z.1) (r.2 z.1) z.2)

/-- For every term choice, the next state has at most as many positions as the old one. The
number of old site and slot records plus selector bits is at most `positions * K * (K +
Nat.clog 2 (maxWireWidth + 1))`. -/
def PassScanBound {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} {W : p.MapWitnesses κ}
    (r : PassReaders p W) (K : ℕ) : Prop :=
  ∀ i, (p.next i).positions ≤ X.positions ∧
    X.positions * (2 ^ a + 1) + (r.select.encode i).length ≤
      X.positions * K * (K + Nat.clog 2 (X.maxWireWidth+1))

/-- Require the same per-pass scan constant at every branch of a state execution. -/
def ScanBound {a g b n : ℕ} {X : State a g} :
    (E : StateExecution R b n X) → (W : E.MapWitnesses κ) → ExecutionReaders E W → ℕ → Prop
  | .done _, _, _, _ => True
  | .more _ tail, W, r, K => PassScanBound r.1 K ∧ ∀ i, ScanBound (tail i) (W.2 i) (r.2 i) K

private theorem scanBound_bind {a g b n b' n' : ℕ} {X : State a g} (E : StateExecution R b n X)
    (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (W : E.MapWitnesses κ) (V : ∀ z, (f z).MapWitnesses κ)
    (r : ExecutionReaders E W) (s : ∀ z, ExecutionReaders (f z) (V z)) (K : ℕ)
    (hr : ScanBound E W r K) (hs : ∀ z, ScanBound (f z) (V z) (s z) K) :
    ScanBound (E.bind f) _ (bindReaders E f W V r s) K := by
  induction E with
  | done => exact hs ()
  | more _ _ ih => exact ⟨hr.1, fun i => ih i _ (W.2 i) _ (r.2 i) _ (hr.2 i) (fun z => hs ⟨i,z⟩)⟩

variable {a b l d K : ℕ} {μ : ℝ}

/-- A uniform per-pass scan bound for every execution of a procedure, over all admissible lane
counts and input states. -/
abbrev ProcedureScanBound {P : Procedure R a b l d μ} {W : P.MapWitnesses κ} (r : ProcedureReaders P W) (K : ℕ) :=
  ∀ g n h X, ScanBound (P.run g n h X) _ (r g n h X) K

namespace ProcedureScanBound

private theorem id (a K : ℕ) (κ : L → R) : ProcedureScanBound (ProcedureReaders.id a κ) K := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g
  trivial

private theorem ofPass {A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)
    (W : ∀ g X, (f g X).MapWitnesses κ) (r : ∀ g X, PassReaders (f g X) (W g X))
    (hr : ∀ g X, PassScanBound (r g X) K) :
    ProcedureScanBound (ProcedureReaders.ofPass hd hμ hA f hc he W r) K := by
  intro g n h X
  subst n
  exact ⟨hr g X, fun _ => trivial⟩

private theorem seq {c l' d' : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {W : P.MapWitnesses κ} {V : Q.MapWitnesses κ} {r : ProcedureReaders P W} {s : ProcedureReaders Q V}
    (hr : ProcedureScanBound r K) (hs : ProcedureScanBound s K) : ProcedureScanBound (r.seq s) K :=
  fun g n eqn X =>
    let E := P.run (l'+g) n (eqn.trans (Nat.add_assoc l l' g)) X
    scanBound_bind E _ _ _ _ _ K (hr _ _ _ X) (fun z => hs _ _ _ (E.finalState z))

private theorem reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {W : P.MapWitnesses κ}
    {r : ProcedureReaders P W} (hr : ProcedureScanBound r K)
    {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    ProcedureScanBound (r.reindex (ha := ha) (hb := hb) (hl := hl) (hd := hd) (hμ := hμ)) K := by
  subst a' b' l' d' μ'
  exact hr

end ProcedureScanBound

open private prefixReaders from OAI.Computability.VPVNP.PairSimulationAssembly
open private prefixWitnesses from OAI.Computability.VPVNP.CompressionMonomialHistory

variable {k : Type*} [Field k] (S : BlockSchedule k)

private theorem prefixScanBound (shrink : S.ShrinkProcedures R) (W : ∀ i, (shrink i).MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (hr : ∀ i, ProcedureScanBound (r i) K) (j : ℕ) (hj : j ≤ S.steps) :
    ProcedureScanBound (prefixReaders S shrink W r j hj) K := by
  induction j with
  | zero =>
    simp only [prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact (ProcedureScanBound.id _ K κ).reindex
  | succ j ih =>
    simp only [prefixReaders, prefixWitnesses, BlockSchedule.shrinkPrefix]
    exact ((ih (Nat.le_of_succ_le hj)).seq (hr ⟨j,hj⟩).reindex).reindex

private theorem assembleScanBound (shrink : S.ShrinkProcedures R) (refresh : S.RefreshProcedure R)
    (W : ∀ i, (shrink i).MapWitnesses κ) (V : refresh.MapWitnesses κ)
    (r : ∀ i, ProcedureReaders (shrink i) (W i)) (s : ProcedureReaders refresh V)
    (h : ∀ i, ProcedureScanBound (r i) K) (h' : ProcedureScanBound s K) :
    ProcedureScanBound (assembleReaders S shrink refresh W V r s) K := by
  unfold assembleReaders
  exact ((prefixScanBound S shrink W r h S.steps le_rfl).reindex.seq h').reindex

private theorem repeatScanBound {P : Procedure R a a l d μ} {W : P.MapWitnesses κ} {r : ProcedureReaders P W}
    (hr : ProcedureScanBound r K) (g T n : ℕ) (h : n = T*l + g) (X : State a n) :
    ScanBound (P.repeatExecution g T n h X) _ (repeatReaders r g T n h X) K := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t*l+g) n (by rw [h, Nat.succ_mul]; omega) X
    exact scanBound_bind E _ _ _ _ _ K (hr _ _ _ X) (fun z => ih _ rfl (E.finalState z))

omit [CommRing R] in
private theorem castAllRecordsLe {N Y Z : Network} (h : N = Y) (c : TermChain R N Z) (v : ℕ)
    (hv : (h ▸ c : TermChain R Y Z).AllRecordsLe v) : c.AllRecordsLe v := by cases h; exact hv

theorem scanUnits_le {a g b n C : ℕ} {X : State a g} (E : StateExecution R b n X) (W : E.MapWitnesses κ)
    (r : ExecutionReaders E W) (rec : E.Records) (z : E.Choices) (K width : ℕ)
    (hr : ScanBound E W r K) (hb : E.Bounded C rec) (hw : X.maxWireWidth ≤ width)
    (hrec : (E.termChain rec z).AllRecordsLe width) :
    scanUnits E W r z ≤ (E.termChain rec z).length * (X.positions * K * (K + Nat.clog 2 (width+1))) := by
  induction E with
  | done => exact Nat.zero_le _
  | @more a g b' n' X p tail ih =>
    let i := z.1
    let Z := (tail i).termChain (rec.2 i) z.2
    let per := X.positions * K * (K + Nat.clog 2 (width+1))
    obtain ⟨hpos, hbits⟩ := hr.1 i
    obtain ⟨fields, maps, htail⟩ := hrec
    have next : (p.next i).maxWireWidth ≤ width := by
      refine (hb.1 i).2.2.trans (Finset.sup_le fun v _ => max_le ?_ ?_)
      · exact Finset.sup_le fun j _ => fields v j
      · exact Finset.sup_le fun j _ => maps v j
    have hc := ih i (W.2 i) (r.2 i) (rec.2 i) z.2 (hr.2 i) (hb.2 i) next (castAllRecordsLe (p.output_eq i).symm Z width htail)
    have hp : X.positions * (2 ^ a + 1) + (r.1.select.encode i).length ≤ per :=
      hbits.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.clog_mono_right 2 (Nat.succ_le_succ hw)) _))
    rw [StateExecution.length_more, Nat.succ_mul, Nat.add_comm]
    exact Nat.add_le_add hp (hc.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right K hpos))))


section Concrete

open MotifGrid MotifBlocks MotifConversion MotifSelector ShrinkMotif Refresh DegreeRefresh

private def capBits {J D E : Type} [Fintype J] [Fintype D] [Fintype E]
    {src dst : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
    (F : FixedBlock k src dst P (realWidths p) (realWidths q) H H') : ℕ :=
  (((∑ i, MotifAdmission.weight p i) + 1) * F.scale * F.radius.num.natAbs * MotifAdmission.denominator q).size

variable {S} (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)

/-- Uniform coefficient for a scan in the fixed block. The width
constant is determined by the two templates; the multiplicities by
the degree schedule and the expander. -/
noncomputable def scanConstant : ℕ :=
  max (1 + max (capBits B.shrink) (capBits B.refresh))
    (max (Finset.univ.sup (fun i : Fin S.steps =>
      let d := 2 ^ S.degreeExponent i.castSucc
      (d + 1) + d * 8))
      ((2 ^ S.portExponent + 1) + 2 ^ S.portExponent * 2 ^ S.expanderExponent))

private theorem scan_charge {n slots atoms bits w k log : ℕ}
    (hcap : w ≤ k + log) (hsize : slots + 1 + atoms ≤ k) (hbits : bits ≤ n * atoms * w) :
    n * (slots+1) + bits ≤ n * k * (k+log) := by
  have hpos : 0 < k+log := by omega
  calc
    _ ≤ n * (slots+1) * (k+log) + n * atoms * (k+log) :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ hpos) (hbits.trans (Nat.mul_le_mul_left _ hcap))
    _ = n * (slots+1+atoms) * (k+log) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsize)

private theorem shrinkMotif_count {a g : ℕ} (X : State a (packingLaneBits a g)) :
    (shrinkMotifOrder X).length ≤ X.positions * (2 ^ a) := by
  have h := Fintype.card_le_of_injective (fun m : X.packingData.Motif => packingInputEdges X.Base a g m.val)
    ((packingInputEdges X.Base a g).injective.comp Subtype.val_injective)
  change Fintype.card X.packingData.Motif ≤ _
  simpa only [State.positions, Fintype.card_prod, Fintype.card_fin] using h

set_option maxHeartbeats 1500000 in
theorem shrinkSelector_bound (i : Fin S.steps) {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) : PassScanBound (shrinkPassReaders B f hf i h X) (scanConstant B) := by
  subst n
  intro s
  let a := S.degreeExponent i.castSucc
  let demand := X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth
  let edges := Order.prod ⟨2, finTwoEquiv⟩ (Order.fin 4)
  let K := scanConstant B
  have hbase : capBits B.shrink ≤ K :=
    (le_max_left _ _).trans ((Nat.le_add_left _ _).trans (le_max_left _ _))
  have hsize : 2^a + 1 + 2^a * 8 ≤ K :=
    (Finset.le_sup (f := fun j : Fin S.steps => 2 ^ S.degreeExponent j.castSucc + 1 +
      2 ^ S.degreeExponent j.castSucc * 8) (Finset.mem_univ i)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc := selectPass_bits_le B.shrink (shrinkMotifOrder X) edges supplyMass_pos demand s
  have hw := selectorWidth_le B.shrink demand X.maxWireWidth
    (X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _) (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth
      (fun _ => X.width_le_maxWireWidth _))
  refine ⟨?_, scan_charge (hw.trans (Nat.add_le_add_right hbase _)) hsize ?_⟩
  · have hcpos := B.shrinkPassAt_positions f hf i rfl X s
    exact (Nat.le_mul_of_pos_left _ (show 0 < packingFactor a by unfold packingFactor; positivity)).trans_eq hcpos.symm
  · change ((selectPass B.shrink (shrinkMotifOrder X) edges supplyMass_pos demand).encode s).length ≤ _
    refine hc.trans ?_
    change (shrinkMotifOrder X).length * (8 * selectorWidth B.shrink demand) ≤ _
    rw [← Nat.mul_assoc, ← Nat.mul_assoc X.positions (2 ^ a) 8]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (shrinkMotif_count X))

private theorem refreshMotif_count {a g : ℕ} (X : State a (a+g)) :
    Fintype.card X.Base * 2 ^ g ≤ X.positions := by
  have hc : ∀ n, Fintype.card (BitWord n) = 2 ^ n := fun n => (Fintype.card_congr (bitWordFinEquiv n)).trans (Fintype.card_fin _)
  rw [State.positions, Fintype.card_prod, hc, pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))

set_option maxHeartbeats 1500000 in
private theorem refreshScanBound : ProcedureScanBound (refreshProcedureReaders B f hf) (scanConstant B) := by
  apply ProcedureScanBound.ofPass
  intro g X c
  let a := S.portExponent
  let demand := blockDemandWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
  let motifs := Order.prod ⟨_, X.baseIndex.symm⟩ ⟨_, (bitWordFinEquiv g).symm⟩
  let edges := (Order.fin (2^a)).prod (Order.fin (2 ^ S.expanderExponent))
  have hq (e : Fin (2^a) × Fin (2^S.expanderExponent)) : 0 < expanderMass S.baseDegree e := by
    unfold expanderMass BlockSchedule.baseDegree
    positivity
  have hcap : capBits B.refresh ≤ scanConstant B :=
    (le_max_right _ _).trans ((Nat.le_add_left _ _).trans (le_max_left _ _))
  have hsize : 2^a+1 + 2^a * 2^S.expanderExponent ≤ scanConstant B :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hw := selectorWidth_le B.refresh demand X.maxWireWidth (fun u j => by
    change internalWidth _ _ u j ≤ _
    unfold internalWidth
    split <;> exact X.width_le_maxWireWidth _)
  refine ⟨(dyadicRefreshNext_positions X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
    B.refresh S.port_order S.degree_bounds.2 c).le, scan_charge (hw.trans (Nat.add_le_add_right hcap _)) hsize ?_⟩
  change ((selectPass B.refresh motifs edges hq demand).encode c).length ≤ _
  refine (selectPass_bits_le B.refresh motifs edges hq demand c).trans ?_
  change (Fintype.card X.Base * 2^g) * (_ * _) ≤ _
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (refreshMotif_count X))

private theorem blockScanBound : ProcedureScanBound (blockReaders B f hf) (scanConstant B) :=
  assembleScanBound S _ _ _ _ _ _ (fun i => ProcedureScanBound.ofPass _ _ _ _ _ _ _ _
    (fun g X => shrinkSelector_bound B f hf i (packingLaneBits_add _ g) X)) (refreshScanBound B f hf)

/-- Scan size on an actual complete selector path. This includes the old
site and outgoing arc records at each pass, and all its choice bits. -/
theorem execute_scanUnits {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    let r := repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X
    scanUnits (B.execute f hf T h X) _ r z ≤ ((S.steps+1)*T) * (X.positions * scanConstant B *
      (scanConstant B + Nat.clog 2 (B.growthConstant ^ T * (X.maxWireWidth+1) + 1))) := by
  let eqn := (Nat.add_sub_of_le h).symm
  let width := B.growthConstant ^ T * (X.maxWireWidth+1)
  have bound := repeatScanBound (blockScanBound B f hf) _ T n eqn X
  obtain ⟨hb, hlen⟩ := Procedure.repeat_recordBounds (B.recordBounds f hf) _ T n eqn X
  obtain ⟨_, _, _, _, hfields, _⟩ := B.branch_bounds f hf T h X z
  have hpos : 0 < B.growthConstant := (by decide : 0 < 2).trans_le B.growthConstant_ge_two
  have hw : X.maxWireWidth ≤ width := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos hpos))
  exact (scanUnits_le _ _ _ _ z (scanConstant B) width bound hb hw hfields).trans (Nat.mul_le_mul_right _ (hlen z))

/-- The descriptor phase reads exactly the admitted sequence of term
choices of the original repeated execution. -/
noncomputable def executeOuterReader {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n) :
    ChoiceReader (B.execute f hf T h X).Choices :=
  ChoiceReader.execution _ (outerReaders _ _ (repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le h).symm X))

theorem executeOuterReader_bits_le {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) :
    ((executeOuterReader B f hf T h X).encode z).length ≤ ((S.steps+1)*T) * (X.positions * scanConstant B *
      (scanConstant B + Nat.clog 2 (B.growthConstant ^ T * (X.maxWireWidth+1) + 1))) :=
  (outerBits_le_scanUnits _ _ _ z).trans (execute_scanUnits B f hf T h X z)

end Concrete
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
