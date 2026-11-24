import OAI.Computability.VPVNP.CompressorRefreshOperandInputs
import OAI.Computability.VPVNP.CompressorRefreshLevelRecipe
import OAI.Computability.VPVNP.CompressorRecordRefreshResult

/-!
# Constructing the refresh argument bank from level and traversal addresses

The two node numbers, their common site ordinal, the private arena and the old inverse
column are traversal inputs. The segment and term heads and the next incidence columns
are evaluated from the same packed level plan used by the native refresh builder. Its
interval frame preserves the old incidence columns through the complete execution.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.OperandInputs

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh NewSlots PhaseRecipe SpectralGeometry
open PairSimulation.NodeArguments RefreshMapOperands

/-- Expressions supplied by the traversal to locate the old and new node arguments at a shared
site ordinal. -/
structure Traversal where
  /-- Expression for the base address of the private node argument arena. -/
  arena : Expr
  /-- Expression for the number of arena words reserved per node. -/
  stride : Expr
  /-- Expression for the child node number indexing the old half of the refresh argument. -/
  child : Expr
  /-- Expression for the parent node number indexing the refreshed half of the argument. -/
  parent : Expr
  /-- Expression for the ordinal shared by the old site and its promoted site. -/
  site : Expr
  /-- Expression for the base of the old actual incoming incidence column. -/
  oldIn : Expr

/-- Builds the child and parent operand records from the traversal addresses and the scratch,
incidence, demand and term columns of the refresh level. -/
def fromLevel (s : LevelRecipe.Shape) (L : LevelRecipe.Input) (J : Traversal) : Input :=
  let q := LevelRecipe.scratch s L
  ⟨⟨J.arena,J.stride,J.child,J.site,J.oldIn,L.oldWidth⟩,
    ⟨J.arena,J.stride,J.parent,J.site,LevelRecipe.column s L 4,LevelRecipe.column s L 5⟩,
    L.lanes,q 5,q 6,q 1,q 7,LevelRecipe.demandStart s L,LevelRecipe.termStart s L⟩

variable {w g : ℕ} (s : LevelRecipe.Shape) (L : LevelRecipe.Input) (J : Traversal) (C : LevelRecipe.Context w)
  (X : State s.a (s.a+g)) (p : (X.Base × BitWord g) × Fin (2^s.a))
  (P : SlotGraph (Fin (2^s.a)) s.dH) (hD : 1 < 2^s.a) (hd : s.dH+1 ≤ 2^s.a₀)
  (internal : X.Base × BitWord g → Fin (2^s.a) × Fin s.dH → ℕ)
  (A : Arena) (child parent start : ℕ) (T : IncidenceDirectory w)

local notation "O" => sites (D := 2^s.a) X.baseIndex (bitWordFinEquiv g)
local notation "plan" => Allocation.plan X s.a₀ s.dH s.ties s.stride start
local notation "Y" => newState X P hD hd internal

private theorem newSite_number : ArgumentAddress.siteOrdinal Y (promotedSites p) = (O p).val := by
  rw [sites_val]
  change (p.2.val + 2^s.a*(X.baseIndex p.1.1).val) * 2^g + (bitWordFinEquiv g p.1.2).val = _
  ring

/-- The packed allocation supplies every numerical operand of the endpoint setup. -/
theorem describes_fromLevel (level : LevelRecipe.Describes L C X start T)
    (base : C.eval J.arena = word A.start) (stride : C.eval J.stride = word A.stride)
    (oldNode : C.eval J.child = word child) (newNode : C.eval J.parent = word parent)
    (site : (C.eval J.site).val = (O p).val) (oldIn : C.eval J.oldIn = T.actualIn) (lanes : 2^g < 2^w) :
    Describes (fromLevel s L J) C.pub C.state C.memory X p P hD hd internal A child parent T ((plan).output w)
      ((plan).scratch w) (word (plan).demand) (word (plan).term) := by
  have heads := LevelRecipe.addresses L C X start T level
  have hs : C.eval J.site = word (O p).val := Fin.ext (site.trans (Nat.mod_eq_of_lt (site ▸ (C.eval J.site).isLt)).symm)
  have oldSite : ArgumentAddress.siteOrdinal X (oldSite X p) = (O p).val := ArgumentSite.oldSite_number X p
  have newSite := newSite_number s X p P hD hd internal
  exact ⟨⟨base,stride,oldNode,oldSite ▸ hs,oldIn,level.oldWidth_eq⟩,
    ⟨base,stride,newNode,newSite ▸ hs,heads.column_eq 4,heads.column_eq 5⟩,
    site,(congrArg Fin.val level.lanes_eq).trans (Nat.mod_eq_of_lt lanes),
    heads.scratch_eq 5,heads.scratch_eq 6,heads.scratch_eq 1,heads.scratch_eq 7,heads.demand_eq,heads.term_eq⟩

/-- Every old incidence read survives the packed refresh. This applies both to the
private operand setup and to future descriptor traversals reaching this older level. -/
theorem old_directory {a g w : ℕ} (X : State a (a+g)) (T : IncidenceDirectory w) (m m' : Memory w)
    (rep : T.Represents X m) (start : ℕ)
    (before : ∀ c : Fin 6, (T.column c).val + Fintype.card X.Base * 2^a * 2^g * 2^a ≤ start)
    (unchanged : ∀ addr < start, m' addr = m addr) : T.Represents X m' := by
  let capacity := Fintype.card X.Base * 2^a * 2^g * 2^a
  have atColumn (c : Fin 6) (j : W w) (hj : j.val < capacity) :
      m' (T.column c+j).val = m (T.column c+j).val :=
    unchanged _ (((Nat.mod_le ..).trans_lt (Nat.add_lt_add_left hj _)).trans_le (before c))
  have baseRoom : Fintype.card X.Base * 2^a ≤ capacity := by
    apply (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g)).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  have base (c : Fin 6) (e) := atColumn c (IncidenceDirectory.basePort X e) (by
    rw [IncidenceDirectory.basePort_number]
    exact (Nat.mod_le ..).trans_lt ((IncidenceDirectory.baseOrder X e).isLt.trans_le baseRoom))
  have total : Fintype.card X.Base*2^(a+g)*2^a = capacity := by dsimp [capacity]; rw [pow_add]; ring
  have actual (c : Fin 6) (e) := atColumn c (IncidenceDirectory.actualPort X e) (by
    rw [IncidenceDirectory.actualPort_number]
    exact (Nat.mod_le ..).trans_lt (total ▸ (IncidenceDirectory.actualOrder X e).isLt))
  exact ⟨fun e => (base 0 e).trans (rep.baseOut e),fun e => (base 1 e).trans (rep.baseIn e),
    fun e => (base 2 e).trans (rep.shift e),fun e => (actual 3 e).trans (rep.actualOut e),
    fun e => (actual 4 e).trans (rep.actualIn e),fun e => (actual 5 e).trans (rep.width e)⟩

/-- Both incidence inputs and all stored fields for the native map and diagonal setups
are available together after the selected refresh level. -/
theorem run_argument_data {k : Type*} [_root_.Field k] {K K' : ℝ} {a a₀ g dH bits t cap : ℕ}
    (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
    (conn : (arcSupportGraph E.multiplicity).Connected)
    (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K') (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀)
    (choice : DyadicRefreshChoice X E hdH conn F) (ties : Fin t ≃ Tie (2^a))
    (T : IncidenceDirectory bits) (start stride : ℕ)
    {L : Allocation.PrepareLayout X T a₀ dH t stride start} {m : Memory bits} {rs : List (Report bits)}
    (execution : Build.Run X E hdH conn F hD hd choice ties T start stride cap L m rs)
    (old : T.Represents X m)
    (before : ∀ c : Fin 6, (T.column c).val + Fintype.card X.Base*2^a*2^g*2^a ≤ start)
    (wide : 2+2^a*dH ≤ stride) (room : (Allocation.plan X a₀ dH t stride start).stop < 2^bits)
    (termBits : termConstant E hdH conn F ties + 4*Nat.clog 2 (X.maxWireWidth+1) ≤ bits)
    (nextWidth : (dyadicRefreshNext X E hdH conn F hD hd choice).maxWireWidth < 2^bits)
    (capFit : TermWorker.budget F t (2^a*dH) bits X.maxWireWidth ≤ cap) :
    let final := after m (eventLog rs)
    T.Represents X final ∧
      ((Allocation.plan X a₀ dH t stride start).output bits).Represents
        (dyadicRefreshNext X E hdH conn F hD hd choice) final ∧
      Build.Stored X E hdH conn F choice ties start stride L.regions.fits final := by
  obtain ⟨rep,stored,frame,_⟩ := Build.Run.result X E hdH conn F hD hd choice ties T start stride execution old
    before wide room termBits nextWidth capFit
  exact ⟨old_directory X T m _ old start before (fun a ha => frame a (Or.inl ha)),rep,stored⟩

end CompressorRecords.PortRefresh.OperandInputs

end VPVNP
end Computability
end OAI
