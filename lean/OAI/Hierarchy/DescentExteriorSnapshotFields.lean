import OAI.Hierarchy.DescentExteriorHopSnapshots
import OAI.Hierarchy.DescentExteriorStaticHops
import OAI.Hierarchy.DescentExteriorPrintedCalendar

namespace OAI
/-! # Authentic per-date literal fields and the retained reset rank banks -/

namespace Hierarchy.DescentExteriorReplay.Snapshots
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {k w : ℕ} (S : Snapshots k)

theorem read_at (base f scratch n age t : ℕ) (first m : Memory w)
    (live : t<age) (early : S.start base f age ≤ scratch)
    (mounted : ∀x<scratch,m x=S.image base f first age x)
    (b : Bank) (end_ : b.base+b.size≤S.start base f (t+1)) (key : Word w) :
    b.read (stage (S.hop base f scratch n) n m t) key =
      b.read (S.image base f first (t+1)) key := by
  apply bank_frame b _ _ key _ end_
  intro x used
  have before := used.trans_le ((S.start_mono base f live).trans early)
  exact (S.stage_frame base f scratch n m t x before).trans
    ((mounted x before).trans (S.previous base f first live used))

theorem literal_fields (base f scratch n age t : ℕ) (first m : Memory w) (live : t<age)
    (early : S.start base f age ≤ scratch) (room : scratch<2^w)
    (mounted : ∀x<scratch,m x=S.image base f first age x) :
    let slot:=S.hop base f scratch n
    let heap:=stage slot n m t
    (∀v:Fin (S.hosts t),(slot t).hostBase.read heap (v.val:Word w)=((v.val*S.pitch t:ℕ):Word w)) ∧
    (∀j:Fin (2^k),(slot t).localShape.read heap (j.val:Word w)=(S.shape t j:Word w)) ∧
    ∀i:Fin n,i.val<2^w→(slot t).frozenDigit.read heap (i.val:Word w)=
      ((((i.val%2^f)/2^(k*t))%2^k:ℕ):Word w) := by
  let low:=S.start base f t
  have fits : low+HopLiteral.words (S.hosts t) k f < 2^w :=
    lt_of_le_of_lt ((S.start_mono base f live).trans early) room
  obtain ⟨h,l,d⟩:=HopLiteral.rooms _ _ _ _ _ fits
  refine ⟨fun v => ?_,fun j => ?_,fun i wide => ?_⟩
  · exact (S.read_at base f scratch n age t first m live early mounted _ h.2.2 _).trans
      (HopLiteral.host_read low _ _ _ _ _ _ _ fits v)
  · exact (S.read_at base f scratch n age t first m live early mounted _ l.2.2 _).trans
      (HopLiteral.shape_read low _ _ _ _ _ _ _ fits j)
  · exact (S.read_at base f scratch n age t first m live early mounted _ d.2.2 _).trans
      (HopLiteral.digit_read low _ _ _ _ _ _ _ _ wide)

theorem previous_rank (base f scratch n age t : ℕ) (first m : Memory w)
    (early : base≤ scratch) (mounted : ∀x<scratch,m x=S.image base f first age x)
    (b : Bank) (prior : b.base+b.size≤base) (key : Word w) :
    b.read (stage (S.hop base f scratch n) n m t) key=b.read first key := by
  apply bank_frame b _ _ key _ prior
  intro x used
  have below:=used.trans_le early
  exact (S.stage_frame base f scratch n m t x below).trans
    ((mounted x below).trans (S.image_frame base f first age x (Or.inl used)))

end Hierarchy.DescentExteriorReplay.Snapshots

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorReplay DescentHostDirectory DescentHostDegree DescentCommonHost DescentDenseHostOrder
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k hwire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ i z D : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ hwire hist}
  {current : Reached W G q ε S k i z D hwire hist}
  (path : Path initial current) (A : Snapshots k)

/-- The only mutable input of a reset snapshot is the rank directory indexed
by that reset's printed old host and local shape. Ordinary dates have no input. -/
def Path.snapshotRanks {bw : ℕ} (before : ℕ) (input : Memory bw) : Prop := by
  induction path with
  | here => exact True
  | @ordinary _ age _ _ _ _ src prev _ _ _ _ _ _ ticket ih =>
    exact ih ∧ A.compact age=none
  | @reset _ age _ Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih =>
    let vertex:=b.frame.host.symm.toEmbedding.trans src.vertex
    exact ih ∧ ∃r,A.compact age=some r ∧ r.Fits bw before ∧
      ∀v,r.read input ((b.reset.rawHostRank b.terminals vertex v).val:Computability.VPVNP.BurstRAM.Word bw)=
        ((b.reset.denseHostRank b.terminals vertex v).val:Computability.VPVNP.BurstRAM.Word bw)

/-- These definitions depend only on the public calendar and its one fixed rotor. -/
def Path.snapshotLabels : Prop := by
  induction path with
  | here => exact True
  | @ordinary _ age _ Di _ _ src prev _ _ _ _ _ _ ticket ih =>
    exact ih ∧ A.pitch age=HopTables.ordinaryPitch k Di ∧ A.shape age=HopTables.ordinaryShape k Di
  | @reset _ age _ Di n h C f g _ _ src prev ctl b ih =>
    exact ih ∧ A.pitch age=HopTables.resetPitch ctl.board k (GroupStage.depthBound Di n f g) ∧
      A.shape age=HopTables.resetShape ctl.board k (GroupStage.depthBound Di n f g) k g

omit [Fintype P] in
theorem Path.snapshot_fields {bw : ℕ} (base f scratch n age : ℕ) (first m : Memory bw)
    (incl : i≤age) (hosts : ∀t<age,S.hostSize t≤A.hosts t)
    (shelf : A.start base f age ≤ scratch) (room : scratch<2^bw)
    (mounted : ∀x<scratch,m x=A.image base f first age x)
    (ranks : path.snapshotRanks A base first) (labels : path.snapshotLabels A) :
    path.shapeFields (count:=n) (A.hop base f scratch n) m := by
  induction path with
  | here => trivial
  | @ordinary _ t _ Di _ _ src prev _ _ _ _ _ _ ticket ih =>
    obtain ⟨past,kind⟩:=ranks
    obtain ⟨old,pitch,local_⟩:=labels
    have reached : t<age := incl
    obtain ⟨h,l,_⟩:=A.literal_fields base f scratch n age t first m reached shelf room mounted
    refine ⟨ih (Nat.le_of_lt reached) past old,kind,fun v => ?_,fun bit => ?_⟩
    · simpa only [pitch, Fin.val_castLE, HopTables.ordinaryPitch, src.branch] using h ((src.vertex v).castLE (src.valid.host.trans (hosts t reached)))
    · simpa only [local_, HopTables.ordinaryShape, src.branch] using l bit
  | @reset _ t _ Di dim gh C₀ f₀ g₀ c₀ t₀ src prev ctl b ih =>
    obtain ⟨past,r,mode,memRoom,forward⟩:=ranks
    obtain ⟨old,pitch,local_⟩:=labels
    have reached : t<age := incl
    obtain ⟨h,l,_⟩:=A.literal_fields base f scratch n age t first m reached shelf room mounted
    obtain ⟨hp,hs⟩:=HopTables.reset_public b
    refine ⟨ih (Nat.le_of_lt reached) past old,r,mode,fun v => ?_,fun bit => ?_,fun v => ?_⟩
    · simpa only [pitch,←hp,Fin.val_castLE] using h ((src.vertex v).castLE (src.valid.host.trans (hosts t reached)))
    · simpa only [local_,←hs] using l bit
    · have low : base≤ scratch := (A.start_mono base f (Nat.zero_le age)).trans shelf
      exact (A.previous_rank base f scratch n age t first m low mounted r memRoom.2.2 _).trans (forward v)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
