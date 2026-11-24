import OAI.Computability.VPVNP.CompressorTermWorkerRecipe
import OAI.Computability.VPVNP.CompressorRecordRefreshAllocation
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe

/-!
# Online row planners for a complete degree refresh

The old base-vertex and residual-lane counts, allocation start, and three
input incidence pointers are expressions over the current level header. The
port degrees, motif strides, role order and expander are fixed for a block.
Every worker's stop cursor and public bank are computed in the planner
before dispatch, in the order used by the native refresh proofs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.LevelRecipe

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open SpectralGeometry PhaseRecipe NewSlots

/-- Dynamic values obtained from the current level header or its inputs. -/
structure Input where
  /-- Expression for the first word of the refresh level's allocation. -/
  start : Expr
  /-- Expression for the number of base vertices in the incoming network. -/
  vertices : Expr
  /-- Expression for the number of residual lanes after the port bits have been split off. -/
  lanes : Expr
  /-- Expression for the head of the incoming state's base outgoing incidence column. -/
  oldOut : Expr
  /-- Expression for the head of the incoming state's lane-shift column. -/
  oldShift : Expr
  /-- Expression for the head of the incoming state's wire-width column. -/
  oldWidth : Expr

/-- The fixed combinatorial and arithmetic parameters of a refresh. -/
structure Shape where
  /-- Number of port bits split from an incoming lane to form the promoted base vertex. -/
  a : ℕ
  /-- Exponent of the dyadic slot degree in the refreshed state. -/
  a₀ : ℕ
  /-- Degree of the expander on the refresh ports. -/
  dH : ℕ
  /-- Number of demand ties enumerated in each base-vertex and residual-lane block. -/
  ties : ℕ
  /-- Number of words reserved for each block's stored motif term. -/
  stride : ℕ
  /-- Width in bits of a selector in the fixed refresh template. -/
  selectors : ℕ

/-- The number of promoted ports, equal to two raised to the input port exponent. -/
abbrev Shape.ports (s : Shape) := 2^s.a
/-- The number of output slots per refreshed vertex, equal to two raised to the new degree
exponent. -/
abbrev Shape.degree (s : Shape) := 2^s.a₀

/-- The dispatcher's physical worker tags. All copies of a fixed worker use
one tag, including every demand row and each public expander ROM row. -/
structure Tags where
  /-- Worker tag for gathering old segment widths. -/
  gather : ℕ
  /-- Worker tag for constructing the directory of external bundles. -/
  bundles : ℕ
  /-- Worker tag for scanning the segment offsets. -/
  offsets : ℕ
  /-- Shared worker tag for the demand scans indexed by ties. -/
  demand : ℕ
  /-- Worker tag for the strided motif-term pass. -/
  term : ℕ
  /-- Worker tag for the scan that reads the selected terms and writes expander supply data. -/
  supply : ℕ
  /-- Shared worker tag for publishing the fixed expander's reverse-incidence entries. -/
  rom : ℕ
  /-- Worker tag for writing the refreshed external slot. -/
  external : ℕ
  /-- Worker tag for writing an internal expander slot. -/
  expander : ℕ
  /-- Worker tag for writing a padding slot of the refreshed degree. -/
  padding : ℕ
  /-- Worker tag for publishing the refreshed base-incidence columns. -/
  base : ℕ

variable (s : Shape) (I : Input)

/-- Expression counting base-vertex, promoted-port and residual-lane triples. -/
def sites := (I.vertices.mul (.lit s.ports)).mul I.lanes
/-- Expression counting base-vertex and residual-lane pairs, one per motif-term record. -/
def blocks := I.vertices.mul I.lanes
/-- Expression counting one old port segment per port at every promoted site. -/
def segments := (sites s I).mul (.lit s.ports)
/-- Expression counting all output incidence slots over the promoted sites. -/
def capacity := (sites s I).mul (.lit s.degree)
/-- Head of the dense demand table, following the seven segment-sized scratch columns. -/
def demandStart := I.start.add ((Expr.lit 7).mul (segments s I))
/-- Head of the strided term records, following all blocks' demand ties. -/
def termStart := (demandStart s I).add ((blocks I).mul (.lit s.ties))
/-- Head of the supply table, following the block term records. -/
def supplyStart := (termStart s I).add ((blocks I).mul (.lit s.stride))
/-- Head of the expander target-port table, following the site-by-expander-slot supply table. -/
def targetPort := (supplyStart s I).add ((sites s I).mul (.lit s.dH))
/-- Head of the expander reverse-slot table, immediately after the target-port table. -/
def reverseSlot := (targetPort s I).add ((Expr.lit s.ports).mul (.lit s.dH))
/-- Head of the refreshed incidence output, immediately after the expander reverse-slot table. -/
def outputStart := (reverseSlot s I).add ((Expr.lit s.ports).mul (.lit s.dH))
/-- Exclusive end of the level allocation after all six output columns. -/
def allocationStop := (outputStart s I).add ((Expr.lit 6).mul (capacity s I))
/-- Base address expression for the indexed output column, spaced by the full incidence
capacity. -/
def column (i : Fin 6) := (outputStart s I).add ((Expr.lit i.val).mul (capacity s I))

/-- The eight scratch operands, consisting of the port count followed by the heads of seven
segment-sized columns. -/
def scratch (i : Fin 8) :=
  if i = 0 then Expr.lit s.ports else I.start.add ((Expr.lit (i.val-1)).mul (segments s I))

/-- The demand head and tie count followed by the term head and stride, supplied to the motif
worker. -/
def termHeads : Fin 4 → Expr := ![demandStart s I,.lit s.ties,termStart s I,.lit s.stride]

/-- A stage of the native refresh calendar, with separate occurrences for each demand tie,
expander ROM entry and output slot. -/
inductive Stage (s : Shape) where
  | gather | bundles | offsets | demand (k : Fin s.ties) | term | supply
  | rom (i : Fin (s.ports*s.dH)) | slot (k : Fin s.degree) | base

/-- The execution order from width gathering and demand scans through term selection, supply,
ROM publication, slot writing and base output. -/
def order : List (Stage s) :=
  [.gather,.bundles,.offsets] ++ (List.finRange s.ties).map Stage.demand ++ [.term,.supply] ++
  (List.finRange (s.ports*s.dH)).map Stage.rom ++ (List.finRange s.degree).map Stage.slot ++ [.base]

variable {s} (tags : Tags) (hd : s.dH+1 ≤ s.degree)

/-- Selects the dispatch tag for a stage, distinguishing the external, expander and padding
cases of a slot. -/
def Stage.tag : Stage s → ℕ
  | .gather => tags.gather
  | .bundles => tags.bundles
  | .offsets => tags.offsets
  | .demand _ => tags.demand
  | .term => tags.term
  | .supply => tags.supply
  | .rom _ => tags.rom
  | .slot k => match kindOf ((refreshSlots hd).symm k) with
    | .external => tags.external
    | .expander => tags.expander
    | .padding => tags.padding
  | .base => tags.base

/-- Number of public operand words used by a stage's native worker, parameterized by the motif
worker's arity. -/
def Stage.arity (termPorts : ℕ) : Stage s → ℕ
  | .gather => 4
  | .bundles | .offsets | .demand _ => 8
  | .term => termPorts
  | .supply => 7
  | .rom _ => 5
  | .slot _ => 13
  | .base => 6

/-- Planner expression for the initial worker cursor, equal to the entry ordinal on a ROM stage
and zero on the other stages. -/
def Stage.initial : Stage s → Expr
  | .rom i => .lit i.val
  | _ => .lit 0

/-- Planner expression for the exclusive stop cursor of a stage, sized to the table it scans. -/
def Stage.stop : Stage s → Expr
  | .gather | .offsets => segments s I
  | .bundles | .slot _ => sites s I
  | .demand _ | .term => blocks I
  | .supply => (sites s I).mul (.lit s.dH)
  | .rom i => .lit (i.val+1)
  | .base => (I.vertices.mul (.lit s.ports)).mul (.lit s.degree)

private def copy {dH d₀ : ℕ} : RefreshSlot dH d₀ → ℕ
  | .inl _ => 0
  | .inr (.inl k) | .inr (.inr k) => k.val

variable {termPorts G : ℕ}
  (E : RegularArcGraph (Fin s.ports) s.dH) (tieOrder : Fin s.ties ≃ Tie s.ports)
  (termBank : (Fin 4 → Expr) → Fin termPorts → Expr)

/-- The public operand expressions of a native stage, including its layout addresses and fixed
expander or tie indices. -/
def Stage.bank : (j : Stage s) → Fin (j.arity termPorts) → Expr
  | .gather => ![scratch s I 0,I.lanes,I.oldWidth,scratch s I 1]
  | .bundles => ![I.lanes,I.oldOut,scratch s I 2,scratch s I 3,scratch s I 4,I.oldShift,.lit 0,.lit 0]
  | .offsets => scratch s I
  | .demand k =>
    let e := tieOrder k
    ![I.lanes,.lit s.ports,.lit (tieTarget e).val,.lit (tieSource e).val,.lit s.ties,.lit k.val,
      if e.1 then scratch s I 1 else scratch s I 7,demandStart s I]
  | .term => termBank (termHeads s I)
  | .supply => ![.lit s.ports,I.lanes,.lit s.dH,termStart s I,.lit s.stride,.lit s.selectors,supplyStart s I]
  | .rom i =>
    let dst := E.reverse (finProdFinEquiv.symm i)
    ![.lit i.val,.lit dst.1.val,.lit dst.2.val,targetPort s I,reverseSlot s I]
  | .slot k => ![.lit s.ports,.lit s.dH,.lit s.degree,I.lanes,.lit (copy ((refreshSlots hd).symm k)),
    scratch s I 2,scratch s I 4,targetPort s I,reverseSlot s I,supplyStart s I,column s I 3,column s I 4,column s I 5]
  | .base => ![.lit s.degree,I.lanes,column s I 3,column s I 0,column s I 1,column s I 2]

private def opPass {r k : ℕ} (ops : List (PrimedStackRAM.Op r k)) (result : Fin r) : Schedule.Pass :=
  ⟨_,_,_,PrimedStackRAM.template ops result⟩

/-- Actual native instruction table of this calendar occurrence. The ROM and
demand tables vary their public literals across occurrences. -/
def Stage.worker (term : Schedule.Pass) : Stage s → Schedule.Pass
  | .gather => opPass RefreshGather.gather 0
  | .bundles => opPass BundleDirectory.visit 0
  | .offsets => Schedule.refreshPass
  | .demand _ => opPass DemandScan.visit 0
  | .term => term
  | .supply => opPass SupplyScan.visit 0
  | .rom _ => opPass ExpanderROM.put 0
  | .slot k => opPass (NewSlots.code (kindOf ((refreshSlots hd).symm k))) 0
  | .base => opPass BaseOutput.visit 0

theorem Stage.worker_params (term : Schedule.Pass) (j : Stage s) :
    (j.worker hd term).params = j.arity term.params := by cases j <;> rfl

/-- Operand formulas indexed directly by the actual worker table's ports. -/
def Stage.workerBank (term : Schedule.Pass)
    (terms : (Fin 4 → Expr) → Fin term.params → Expr) (j : Stage s) :
    Fin (j.worker hd term).params → Expr :=
  fun i => j.bank I hd E tieOrder terms (Fin.cast (j.worker_params hd term) i)

private theorem arity_le (room : max 13 termPorts ≤ G) (j : Stage s) : j.arity termPorts ≤ G := by
  cases j <;> simp only [Stage.arity] <;> omega

/-- The phase installed by the expression compiler for one fixed stage. -/
def phase (room : max 13 termPorts ≤ G) (j : Stage s) : Phase G :=
  Phase.ofParams (arity_le room j) (j.tag tags hd) j.initial (j.stop I) (j.bank I hd E tieOrder termBank)

/-- The entire fixed list of online planners, including one strided term scan. -/
def phases (room : max 13 termPorts ≤ G) : List (Phase G) :=
  (order s).map (phase I tags hd E tieOrder termBank room)

/-- A refresh adds a fixed number of rows to the block calendar regardless of
the incoming network size and the word width. -/
theorem phases_length (room : max 13 termPorts ≤ G) :
    (phases I tags hd E tieOrder termBank room).length =
      6 + s.ties + s.ports*s.dH + s.degree := by
  simp [phases,order]; omega

/-- The public inputs, state word and memory against which a level's planner expressions are
evaluated. -/
structure Context (w : ℕ) where
  /-- The five public input words available to a refresh planner expression. -/
  pub : Fin 5 → W w
  /-- The state word available to the refresh planner during expression evaluation. -/
  state : W w
  /-- The memory read by load expressions in the refresh level planner. -/
  memory : Memory w

variable {w g : ℕ} (C : Context w)

/-- Evaluates a planner expression with the context's public words, state and memory. -/
abbrev Context.eval (e : Expr) := e.eval C.pub C.state C.memory

/-- Meaning of the six dynamic expressions. The rest of the row values
follow from these six input words and the fixed template. -/
structure Describes (X : State s.a (s.a+g)) (start : ℕ) (old : IncidenceDirectory w) : Prop where
  start_eq : C.eval I.start = word start
  vertices_eq : C.eval I.vertices = word (Fintype.card X.Base)
  lanes_eq : C.eval I.lanes = word (2^g)
  oldOut_eq : C.eval I.oldOut = old.baseOut
  oldShift_eq : C.eval I.oldShift = old.shift
  oldWidth_eq : C.eval I.oldWidth = old.width

variable (X : State s.a (s.a+g)) (start : ℕ) (old : IncidenceDirectory w)
local notation "P" => Allocation.plan X s.a₀ s.dH s.ties s.stride start

private theorem eval_lit (n : ℕ) : C.eval (.lit n) = word n := rfl
private theorem eval_add (x y : Expr) : C.eval (x.add y) = C.eval x + C.eval y := rfl
private theorem eval_mul (x y : Expr) : C.eval (x.mul y) = C.eval x * C.eval y := rfl
private theorem word_add (x y : ℕ) : word x + word y = word (bits := w) (x+y) :=
  Fin.ext (Nat.add_mod x y _).symm
private theorem word_mul (x y : ℕ) : word x * word y = word (bits := w) (x*y) :=
  Fin.ext (Nat.mul_mod x y _).symm

/-- Correspondence of the computed addresses with the packed allocation
used by the descriptor correctness proof. Word reduction is valid at every
intermediate arithmetic operation. -/
structure Addresses (p : Allocation.Plan) : Prop where
  sites_eq : C.eval (sites s I) = word p.sites
  blocks_eq : C.eval (blocks I) = word p.blocks
  segments_eq : C.eval (segments s I) = word p.segments
  capacity_eq : C.eval (capacity s I) = word p.capacity
  demand_eq : C.eval (demandStart s I) = word p.demand
  term_eq : C.eval (termStart s I) = word p.term
  supply_eq : C.eval (supplyStart s I) = word p.supply
  target_eq : C.eval (targetPort s I) = word p.targetPort
  reverse_eq : C.eval (reverseSlot s I) = word p.reverseSlot
  output_eq : C.eval (outputStart s I) = word p.next
  stop_eq : C.eval (allocationStop s I) = word p.stop
  scratch_eq : ∀ i, C.eval (scratch s I i) = p.scratch w i
  column_eq : ∀ i, C.eval (column s I i) = (p.output w).column i

theorem addresses (h : Describes I C X start old) : Addresses (s := s) I C P := by
  have hs : C.eval (sites s I) = word (P).sites := by
    simp only [sites,eval_mul,eval_lit,h.vertices_eq,h.lanes_eq,word_mul]; rfl
  have hb : C.eval (blocks I) = word (P).blocks := by
    simp only [blocks,eval_mul,h.vertices_eq,h.lanes_eq,word_mul]; rfl
  have seg : C.eval (segments s I) = word (P).segments := by
    simp only [segments,eval_mul,hs,eval_lit,word_mul]; rfl
  have cap : C.eval (capacity s I) = word (P).capacity := by
    simp only [capacity,eval_mul,hs,eval_lit,word_mul]; rfl
  have dem : C.eval (demandStart s I) = word (P).demand := by
    simp only [demandStart,eval_add,eval_mul,h.start_eq,eval_lit,seg,word_mul,word_add]; rfl
  have trm : C.eval (termStart s I) = word (P).term := by
    simp only [termStart,eval_add,eval_mul,dem,hb,eval_lit,word_mul,word_add]; rfl
  have sup : C.eval (supplyStart s I) = word (P).supply := by
    simp only [supplyStart,eval_add,eval_mul,trm,hb,eval_lit,word_mul,word_add]; rfl
  have tgt : C.eval (targetPort s I) = word (P).targetPort := by
    simp only [targetPort,eval_add,eval_mul,sup,hs,eval_lit,word_mul,word_add]; rfl
  have rev : C.eval (reverseSlot s I) = word (P).reverseSlot := by
    simp only [reverseSlot,eval_add,eval_mul,tgt,eval_lit,word_mul,word_add]; rfl
  have nxt : C.eval (outputStart s I) = word (P).next := by
    simp only [outputStart,eval_add,eval_mul,rev,eval_lit,word_mul,word_add]; rfl
  have stop : C.eval (allocationStop s I) = word (P).stop := by
    simp only [allocationStop,eval_add,eval_mul,nxt,eval_lit,cap,word_mul,word_add]; rfl
  refine ⟨hs,hb,seg,cap,dem,trm,sup,tgt,rev,nxt,stop,fun i => ?_,fun i => ?_⟩
  · by_cases hi : i=0 <;> simp only [scratch,Allocation.Plan.scratch,hi,↓reduceIte,eval_add,eval_mul,
      eval_lit,h.start_eq,seg,word_mul,word_add] <;> rfl
  · rw [Allocation.Plan.output_column]
    simp only [column,eval_add,eval_mul,nxt,eval_lit,cap,word_mul,word_add]

/-- The natural starting cursor used by the native stage, with a ROM entry starting at its own
ordinal. -/
def Stage.first : Stage s → ℕ
  | .rom i => i.val
  | _ => 0

/-- The exclusive natural cursor bound for a native stage, computed from the incoming state and
the level allocation. -/
def Stage.limit : Stage s → ℕ
  | .gather | .offsets => (P).segments
  | .bundles | .slot _ => (P).sites
  | .demand _ | .term => (P).blocks
  | .supply => (P).sites * s.dH
  | .rom i => i.val+1
  | .base => Fintype.card X.Base * s.ports * s.degree

/-- The public words consumed by the already checked native worker proofs. -/
def Stage.nativeBank (termWords : (Fin 4 → W w) → Fin termPorts → W w) :
    (j : Stage s) → Fin (j.arity termPorts) → W w
  | .gather => gatherWords ((P).scratch w) (word (2^g)) old.width
  | .bundles => directoryWords ((P).scratch w) (word (2^g)) old.baseOut old.shift
  | .offsets => (P).scratch w
  | .demand k => DemandScan.words (r := 2^g) tieOrder ((P).scratch w) (word (P).demand) k
  | .term => termWords ![word (P).demand,word s.ties,word (P).term,word s.stride]
  | .supply => SupplyScan.params s.ports (2^g) s.dH (word (P).term) s.stride s.selectors (word (P).supply)
  | .rom i => ExpanderROM.words E ((P).inputs w) i
  | .slot k => AllSlots.words s.ports (2^g) ((P).inputs w) ((P).output w) ((refreshSlots hd).symm k)
  | .base => BaseOutput.params ((P).output w) s.a₀ g

theorem counters (h : Describes I C X start old) (j : Stage s) :
    C.eval j.initial = word j.first ∧ C.eval (j.stop I) = word (j.limit X start) := by
  have ha := addresses I C X start old h
  cases j with
  | supply => exact ⟨rfl,by simp only [Stage.stop,Stage.limit,eval_mul,ha.sites_eq,eval_lit,word_mul]⟩
  | base => exact ⟨rfl,by simp only [Stage.stop,Stage.limit,eval_mul,eval_lit,h.vertices_eq,word_mul]⟩
  | gather | offsets => exact ⟨rfl,ha.segments_eq⟩
  | bundles | slot _ => exact ⟨rfl,ha.sites_eq⟩
  | demand _ | term => exact ⟨rfl,ha.blocks_eq⟩
  | rom _ => exact ⟨rfl,rfl⟩

theorem termHeads_eq (h : Describes I C X start old) :
    (fun i => C.eval (termHeads s I i)) = ![word (P).demand,word s.ties,word (P).term,word s.stride] := by
  have ha := addresses I C X start old h
  funext i
  fin_cases i <;> first | exact ha.demand_eq | exact ha.term_eq | rfl

variable (termWords : (Fin 4 → W w) → Fin termPorts → W w)

theorem banks (h : Describes I C X start old)
    (ht : (fun i => C.eval (termBank (termHeads s I) i)) = termWords (fun i => C.eval (termHeads s I i)))
    (j : Stage s) (i : Fin (j.arity termPorts)) :
    C.eval (j.bank I hd E tieOrder termBank i) = j.nativeBank hd E tieOrder X start old termWords i := by
  have ha := addresses I C X start old h
  cases j with
  | gather =>
    fin_cases i <;> first | exact ha.scratch_eq 0 | exact ha.scratch_eq 1 | exact h.lanes_eq | exact h.oldWidth_eq
  | bundles =>
    fin_cases i <;> first
      | exact ha.scratch_eq 2 | exact ha.scratch_eq 3 | exact ha.scratch_eq 4
      | exact h.lanes_eq | exact h.oldOut_eq | exact h.oldShift_eq | rfl
  | offsets => exact ha.scratch_eq i
  | demand k =>
    have choice :
        C.eval (if (tieOrder k).1 then scratch s I 1 else scratch s I 7) =
          (if (tieOrder k).1 then (P).scratch w 1 else (P).scratch w 7) := by
      cases (tieOrder k).1 <;> first | exact ha.scratch_eq 1 | exact ha.scratch_eq 7
    fin_cases i <;> first | exact h.lanes_eq | exact choice | exact ha.demand_eq | rfl
  | term => exact (congrFun ht i).trans (congrFun (congrArg termWords (termHeads_eq I C X start old h)) i)
  | supply =>
    fin_cases i <;> first | exact h.lanes_eq | exact ha.term_eq | exact ha.supply_eq | rfl
  | rom _ =>
    fin_cases i <;> first | exact ha.target_eq | exact ha.reverse_eq | rfl
  | slot k =>
    fin_cases i <;> first
      | exact h.lanes_eq | exact ha.target_eq | exact ha.reverse_eq | exact ha.supply_eq
      | exact ha.scratch_eq 2 | exact ha.scratch_eq 4 | exact ha.column_eq _ | rfl
  | base => fin_cases i <;> first | exact h.lanes_eq | exact ha.column_eq _ | rfl

/-- Exact field list installed by the compiled planner for this native worker.
The common catalog bank is zero-padded past the worker's own arity. -/
def Stage.fields (j : Stage s) : List (W w) :=
  word (j.tag tags hd) :: word j.first :: word (j.limit X start) :: List.ofFn (fun i : Fin G =>
    if h : i.val < j.arity termPorts then j.nativeBank hd E tieOrder X start old termWords ⟨i.val,h⟩ else 0)

theorem compiled_fields (h : Describes I C X start old)
    (ht : (fun i => C.eval (termBank (termHeads s I) i)) = termWords (fun i => C.eval (termHeads s I i)))
    (room : max 13 termPorts ≤ G) (j : Stage s) :
    (phase I tags hd E tieOrder termBank room j).recipe.words C.pub C.state C.memory =
      j.fields (G := G) tags hd E tieOrder X start old termWords := by
  rw [recipe_words]
  obtain ⟨lo,hi⟩ := counters I C X start old h j
  change word (j.tag tags hd) :: C.eval j.initial :: C.eval (j.stop I) ::
    List.ofFn (fun i : Fin G => C.eval ((phase I tags hd E tieOrder termBank room j).params i)) = _
  rw [lo,hi]
  unfold Stage.fields
  congr 3
  apply congrArg List.ofFn
  funext i
  by_cases used : i.val < j.arity termPorts
  · simp only [phase,Phase.ofParams,used,↓reduceDIte]
    exact banks I hd E tieOrder termBank C X start old termWords h ht j ⟨i.val,used⟩
  · simp only [phase,Phase.ofParams,used,↓reduceDIte]
    rfl

/-- With sufficient cursor space, the planner's two counter fields are the
exact natural start and stop, including the singleton ROM interval. -/
theorem counter_values (h : Describes I C X start old) (j : Stage s)
    (fits : j.limit X start < 2^w) :
    (C.eval j.initial).val = j.first ∧ (C.eval (j.stop I)).val = j.limit X start := by
  obtain ⟨lo,hi⟩ := counters I C X start old h j
  rw [lo,hi]
  have le : j.first ≤ j.limit X start := by cases j <;> simp [Stage.first,Stage.limit]
  exact ⟨Nat.mod_eq_of_lt (le.trans_lt fits),Nat.mod_eq_of_lt fits⟩

include hd in
/-- Every stop cursor fits whenever the complete level allocation fits. The
proof includes the last expander ROM cursor and the lane-zero base pass. -/
theorem limit_fits (allocated : (P).stop ≤ 2^w) (j : Stage s) : j.limit X start < 2^w := by
  have capPos : 0 < (P).capacity := by
    change 0 < Fintype.card X.Base * 2^s.a * 2^g * 2^s.a₀
    positivity
  have capLt : (P).capacity < 2^w := by change (P).next+6*(P).capacity ≤ _ at allocated; omega
  have segLt : (P).segments < 2^w := by
    dsimp only [Allocation.Plan.stop,Allocation.Plan.next,Allocation.Plan.reverseSlot,
      Allocation.Plan.targetPort,Allocation.Plan.supply,Allocation.Plan.term,Allocation.Plan.demand] at allocated
    omega
  have siteLe : (P).sites ≤ (P).capacity := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have blockLe : (P).blocks ≤ (P).sites := by
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have supplyLe : (P).sites * s.dH ≤ (P).capacity := Nat.mul_le_mul_left _ (by omega : s.dH ≤ s.degree)
  have portLe : s.ports ≤ (P).sites := (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))
  cases j with
  | gather | offsets => exact segLt
  | bundles | slot _ => exact siteLe.trans_lt capLt
  | demand _ | term => exact (blockLe.trans siteLe).trans_lt capLt
  | supply => exact supplyLe.trans_lt capLt
  | rom i =>
    exact ((Nat.succ_le_of_lt i.isLt).trans (Nat.mul_le_mul_right _ portLe)).trans_lt (supplyLe.trans_lt capLt)
  | base =>
    exact (Nat.mul_le_mul_right s.degree
      (Nat.le_mul_of_pos_right (Fintype.card X.Base * s.ports) (Nat.two_pow_pos g))).trans_lt capLt

open MotifConversion

variable {k : Type*} [_root_.Field k] {K K' : ℝ} (hdH : 0 < s.dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) s.degree K K')

theorem base_limit_eq (hD : 1 < s.ports) (choice : DyadicRefreshChoice X E hdH conn F) :
    (Stage.base : Stage s).limit X start = BaseOutput.baseCount (dyadicRefreshNext X E hdH conn F hD hd choice) := by
  change Fintype.card X.Base * s.ports * s.degree = Fintype.card (X.Base × Fin s.ports) * s.degree
  simp [Fintype.card_prod]

theorem supply_bank_eq (selectorWidth : s.selectors = F.selectorBits) :
    (Stage.supply : Stage s).nativeBank hd E tieOrder X start old termWords =
      SupplyScan.params s.ports (2^g) s.dH (word (P).term) s.stride F.selectorBits (word (P).supply) := by
  change SupplyScan.params _ _ _ _ _ s.selectors _ = _
  rw [selectorWidth]

/-- The motif worker supplies one phase for all blocks. Its address prefix is
computed online and the remaining grid and arithmetic operands are fixed
natural literals, independent of word width. -/
noncomputable def motifPhases
    (room : max 13 (TermWorker.motifPass F tieOrder (s.ports*s.dH)).params ≤ G) : List (Phase G) :=
  phases I tags hd E tieOrder (TermWorker.motifExprs F tieOrder finProdFinEquiv.symm) room

theorem motif_compiled_fields (h : Describes I C X start old)
    (room : max 13 (TermWorker.motifPass F tieOrder (s.ports*s.dH)).params ≤ G) (j : Stage s) :
    let terms := TermWorker.motifExprs F tieOrder finProdFinEquiv.symm
    (phase I tags hd E tieOrder terms room j).recipe.words C.pub C.state C.memory =
      j.fields (G := G) tags hd E tieOrder X start old (TermWorker.motifData F tieOrder finProdFinEquiv.symm w) :=
  compiled_fields I tags hd E tieOrder _ C X start old _ h
    (TermWorker.eval_motifExprs F tieOrder finProdFinEquiv.symm (termHeads s I) C.pub C.state C.memory) room j

/-- The occurrence-indexed registry may assign the tag after enumerating the
stages. Its public operands still agree pointwise with the native proof for
the fused motif worker or the selected deterministic worker. -/
theorem motif_workerBank_eq (h : Describes I C X start old) (j : Stage s) :
    let term := TermWorker.motifPass F tieOrder (s.ports*s.dH)
    let terms := TermWorker.motifExprs F tieOrder finProdFinEquiv.symm
    ∀ i : Fin (j.worker hd term).params, C.eval (j.workerBank I hd E tieOrder term terms i) =
      j.nativeBank hd E tieOrder X start old (TermWorker.motifData F tieOrder finProdFinEquiv.symm w)
        (Fin.cast (j.worker_params hd term) i) := by
  intro term terms i
  exact banks I hd E tieOrder terms C X start old _ h
    (TermWorker.eval_motifExprs F tieOrder finProdFinEquiv.symm (termHeads s I) C.pub C.state C.memory) j _

/-- The native planner installs the checked public operands, start and stop
for any selected stage of the fixed motif schedule. -/
theorem execute_motif_phase (h : Describes I C X start old)
    (room : max 13 (TermWorker.motifPass F tieOrder (s.ports*s.dH)).params ≤ G) (j : Stage s)
    (cap : ℕ) (budget : (phase I tags hd E tieOrder
      (TermWorker.motifExprs F tieOrder finProdFinEquiv.symm) room j).recipe.code.length < cap)
    (rowRoom : (Controller.rowBase G C.pub C.memory).val + (G+3) ≤ 2^w) :
    let ph := phase I tags hd E tieOrder (TermWorker.motifExprs F tieOrder finProdFinEquiv.symm) room j
    let M := ph.recipe.acceptTable.instantiate w C.pub
    let es := (ph.recipe.report C.pub C.state C.memory).events
    execute M.program cap (M.program.start C.state) C.memory [] = some ⟨es,none⟩ ∧
      Greedy.Stores (after C.memory es) (Controller.rowBase G C.pub C.memory)
        (j.fields (G := G) tags hd E tieOrder X start old (TermWorker.motifData F tieOrder finProdFinEquiv.symm w)) ∧
      (∀ a, a < (Controller.rowBase G C.pub C.memory).val ∨ (Controller.rowBase G C.pub C.memory).val + (G+3) ≤ a →
        after C.memory es a = C.memory a) ∧ countProbes es = ph.recipe.reads+(G+3) ∧ choiceBits es = [] := by
  intro ph M es
  have exactRow := motif_compiled_fields I tags hd E tieOrder C X start old hdH conn F h room j
  change ph.recipe.words C.pub C.state C.memory = _ at exactRow
  rw [recipe_words] at exactRow
  rw [← exactRow]
  exact execute_phase ph C.pub C.state C.memory cap budget rowRoom

end CompressorRecords.PortRefresh.LevelRecipe

end VPVNP
end Computability
end OAI
