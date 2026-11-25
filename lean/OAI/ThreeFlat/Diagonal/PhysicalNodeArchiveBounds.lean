import OAI.ThreeFlat.Diagonal.InitialMetadataSpace
import OAI.ThreeFlat.Diagonal.PhysicalNodeArena
import OAI.ThreeFlat.Diagonal.PublicationLayerBounds
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveRun
import OAI.ThreeFlat.Diagonal.NavigationResources

namespace OAI
/-! # Word bounds for publishing the actual chronological cursor-node archive -/

noncomputable section
namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory
open scoped Classical
variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
/-- The three loop caps of the installed node writer use one fixed coefficient
of the block, independently of the residual width and repetition count. -/
theorem installed_caps (B : Block F) (p : Parameters) (blocks rem W : ℕ) :
    let A := p.archive (2^B.exponent 0) W
    let N := p.nodeArchive A ((B.repeat blocks).directory rem p.axes) W
    max N.childCap (max N.halfCap N.motifCap)≤directoryCap B := by
  let A := p.archive (2^B.exponent 0) W
  let ss := (B.repeat blocks).directory rem p.axes
  let N := p.nodeArchive A ss W
  have c : N.childCap≤directoryCap B := directory_cap B blocks rem p.axes 0 0 (Nat.zero_le _)
  have h : N.halfCap≤directoryCap B := directory_cap B blocks rem p.axes 1 (2*2^B.exponent 0) le_rfl
  have m : N.motifCap≤directoryCap B := directory_cap B blocks rem p.axes 2 0 (Nat.zero_le _)
  exact max_le c (max_le h m)

/-- The actual installed caps, lane and pair counts, and every prefix
multiplication fit in one native word. The remaining inputs here are the
physical ranges of this particular chronological layer. -/
theorem cursor_bounds_of_ranges (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (fixed : directoryCap B≤u)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let N := p.nodeArchive A ((B.repeat (u^8)).directory rem p.axes) W
    ∀ (s : Layer) (par : Parent) (hdr : ℕ),
      N.banks.current<N.banks.charges → hdr+16≤N.banks.charges →
      N.banks.charges+2*(s.first+s.count)≤N.banks.nodes →
      N.banks.nodes+8*(s.first+s.count)<2^W →
      (par.finalLayer=false → par.owners+s.count≤N.banks.charges) →
      s.childCount≤N.childCap →
      Bounds W N.banks s par hdr N.childCap N.halfCap N.motifCap := by
  intro W p A N s par hdr current header chargeEnd nodeEnd ownerEnd arity
  let k := (B.repeat (u^8)).charge+rem
  have pos : 0<u := by omega
  have one : 0<u^10 := Nat.pow_pos pos
  have u10 : u≤u^10 := Nat.le_self_pow (by decide) u
  have u6 : u^6≤u^10 := Nat.pow_le_pow_right pos (by decide)
  have exponent : k+low<W := by dsimp only [W,k];omega
  have large : 2^4<(2:ℕ)^W :=
    Nat.pow_lt_pow_right (by decide) (by dsimp only [W];omega)
  have space : u<2^W := by
    apply (show u≤W by dsimp only [W];omega).trans_lt
    exact Nat.lt_two_pow_self
  have lane : 2^k<2^W := Nat.pow_lt_pow_right (by decide) (by omega)
  have perLane : 2^low<2^W := Nat.pow_lt_pow_right (by decide) (by omega)
  have input : 2*shape.halfBits<2^W :=
    pairs.trans_lt (Nat.pow_lt_pow_right (by decide) (by dsimp only [W];omega))
  have all : max N.childCap (max N.halfCap N.motifCap)<2^W :=
    ((installed_caps B p (u^8) rem W).trans fixed).trans_lt space
  refine ⟨large,current,header,chargeEnd,nodeEnd,ownerEnd,arity,all,lane,input,perLane,?_⟩
  intro j _ active
  change j.val<2^k at active
  change j.val*2^low<2^W
  calc
    j.val*2^low < 2^k*2^low := Nat.mul_lt_mul_of_pos_right active (Nat.two_pow_pos _)
    _ = 2^(k+low) := (pow_add _ _ _).symm
    _ < 2^W := Nat.pow_lt_pow_right (by decide) exponent

/-- Every actual node header of the repeat directory satisfies the physical
publisher's complete bounds for its corresponding charge, node, and owner rows. -/
theorem cursor_bounds (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (fixed : directoryCap B≤u)
    (levels : B.levels+1≤u) (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let P := B.repeat (u^8)
    let ss := P.directory rem p.axes
    let N := p.nodeArchive A ss W
    let rows := nodeLayers A.K ss A.cursor A.seedLayer
    ∀ i : Fin rows.length, let row := rows.get i
      Bounds W N.banks row.actual row.parent (N.headerBase+16*i.val) N.childCap N.halfCap N.motifCap := by
  intro W p A P ss N rows i row
  have space := Parameters.node_publication_arena B u rem low stride cells shape off tariff
    hu levels factor half depth
  have member : row∈rows := List.get_mem rows i
  have span := space.span row member
  have endHeader := (node_header_end N.headerBase rows i).trans space.header
  have owner (nf : row.parent.finalLayer=false) : row.parent.owners+row.actual.count≤N.banks.charges :=
    (program_ownerEnd P A.K rem p.axes A.cursor A.seedLayer rfl row member nf).trans space.heap
  exact cursor_bounds_of_ranges B (rem:=rem) (low:=low) (stride:=stride) (cells:=cells)
    (off:=off) (tariff:=tariff) shape hu fixed depth pairs row.actual row.parent
    (N.headerBase+16*i.val) space.current endHeader span.1 span.2 owner (seed_childArity A ss row member)

end ThreeFlat.Diagonal.NavigationPass.NodePublication
end

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory
open RAM.HistoryStageBody.Physical (resources resources_seq resources_scan)
variable {F : Type} [Field F] [Fintype F]

/-- One charge scan, one eight-column node scan and the actual pointer advance. -/
theorem ticks_le_resources (W : ℕ) (b : Banks) (cc hc mc n : ℕ) :
    ticks W b cc hc mc n ≤
      10*resources (NavigationNodeRows.procedure (W:=W) b cc hc mc)*(n+1) := by
  let S:=resources (NavigationNodeRows.procedure (W:=W) b cc hc mc)
  let cq:=(HeaderScan.closed (w:=W) (charge b cc hc mc)).binds
  let nq:=(HeaderScan.closed (w:=W) (node b)).binds
  have size : S=(18+4*cq)+((18+4*nq)+9) := by
    simp only [S,NavigationNodeRows.procedure,resources_seq,resources_scan];rfl
  have c : 2*cq+4≤S := by omega
  have k : 2*nq+4≤S := by omega
  change (13+2*n*(2*cq+4))+((13+8*n*(2*nq+4))+6) ≤ 10*S*(n+1)
  nlinarith only [Nat.mul_le_mul_left (2*n) c,Nat.mul_le_mul_left (8*n) k,
    (show 32≤10*S by omega)]

/-- An actual scalar clock for the complete physical publication. It includes the packed
header decoder, both startup writes, the counted visits and the exit of that loop. -/
theorem cursor_run_budget (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (fixed : directoryCap B≤u)
    (fixedTime : 10*nodeWriterBudget B≤u) (levels : B.levels+1≤u)
    (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (pairs : 2*shape.halfBits≤2^(3*u^10)) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let P := B.repeat (u^8)
    let ss := P.directory rem p.axes
    let N := p.nodeArchive A ss W
    let rows := nodeLayers A.K ss A.cursor A.seedLayer
    let chunk := 2^(u^10-u^4)
    let budget := u*(chunk+1)
    RunBounds W N rows budget ∧
      ((16*rows.length*(5*W+6)+10)+(3+(3+(rows.length*(7+budget)+4))))≤3000*u^20*chunk := by
  intro W p A P ss N rows chunk budget
  let v:=u^10
  have hpos : 0<u := by omega
  have vpos : 0<v := Nat.pow_pos hpos
  have us : u≤v := Nat.le_self_pow (by decide) _
  have ch : 0<chunk := Nat.two_pow_pos _
  have nrows : ss.length≤u^9 := by
    change ((B.repeat (u^8)).directory rem p.axes).length≤u^9
    rw [Program.directory_length,program_length,B.repeat_effects_length]
    exact (Nat.mul_le_mul_right _ levels).trans_eq (by ring)
  have len : rows.length≤2*v := by
    have eq : rows.length=ss.length+1 := nodeLayers_length _ _ _ _
    have h9 : u^9≤v := Nat.pow_le_pow_right hpos (by decide)
    omega
  have counts := node_count_space B p hu levels factor half depth (by rfl)
  have count (i : Fin rows.length) : (rows.get i).actual.count≤chunk := by
    have all := counts.1 (rows.get i) (List.get_mem rows i)
    change 8*((rows.get i).actual.first+(rows.get i).actual.count)≤chunk at all
    omega
  have space := Parameters.node_publication_arena B u rem low stride cells shape off tariff
    hu levels factor half depth
  have ctrl : N.counter<N.headerBase := space.counter
  have headerSpace : N.headerBase+16*rows.length≤N.banks.charges := space.header
  have cfit : N.banks.charges+2*((rows.map (fun q=>q.actual.count)).sum)≤N.banks.nodes := space.chargeEnd
  have nfit : N.banks.nodes+8*((rows.map (fun q=>q.actual.count)).sum)<2^W := space.nodeEnd
  have curr : N.banks.current<N.banks.charges := space.current
  refine ⟨⟨by omega,by change N.banks.current+3≠N.banks.current;omega,by omega,by omega,
    by omega,cursor_bounds B shape hu fixed levels factor half depth pairs,?_⟩,?_⟩
  · intro i
    have res := node_writer_resources B p (u^8) rem W
    have line : 10*resources (NavigationNodeRows.procedure (W:=W) N.banks N.childCap N.halfCap N.motifCap)≤u :=
      (Nat.mul_le_mul_left 10 res).trans fixedTime
    exact (ticks_le_resources _ _ _ _ _ _).trans (Nat.mul_le_mul line (Nat.succ_le_succ (count i)))
  · have bind : 5*W+6≤86*v := by change 5*(16*v)+6≤86*v;omega
    have cap : 7+budget≤9*v*chunk := by
      have b : budget≤v*(2*chunk) := Nat.mul_le_mul us (by omega)
      have vc : 1≤v*chunk := Nat.mul_pos vpos ch
      change 7+budget≤9*v*chunk
      nlinarith only [b,vc]
    have spare : v*v≤v*v*chunk := Nat.le_mul_of_pos_right _ ch
    have nonempty : 1≤v*v*chunk := Nat.mul_pos (Nat.mul_pos vpos vpos) ch
    calc
      _ ≤ (16*(2*v)*(86*v)+10)+(3+(3+((2*v)*(9*v*chunk)+4))) := by gcongr
      _ ≤ 3000*u^20*chunk := by
        rw [show u^20=v*v by dsimp [v];ring]
        nlinarith only [spare,nonempty]

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows PhysicalStage NavigationDirectory
variable {F : Type} [Field F] [Fintype F]

/-- All selected step records, including the initial metadata in S49, survive the
entire mounted node publication. The low side includes the remaining raw public prefix. -/
theorem cursor_record_addresses (B : Block F) {u rem low stride cells off tariff : ℕ}
    (shape : PhysicalPinsExpr.Shape) (hu : 40≤u) (fixed : directoryCap B≤u)
    (levels : B.levels+1≤u) (factor : B.allocations.sum≤u) (half : low=u^10/2)
    (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) :
    let W := 16*u^10
    let p := Parameters.cursor B u rem low stride cells shape off tariff
    let A := p.archive (2^B.exponent 0) W
    let ss := (B.repeat (u^8)).directory rem p.axes
    let N := p.nodeArchive A ss W
    let rows := nodeLayers A.K ss A.cursor A.seedLayer
    ∀ x : ℕ, x<(finish A.K ss A.cursor).heap ∨ (A.initialRecords≤x ∧ x<A.metadataEnd) →
      x<2^W ∧ stable N rows x ∧
        ∀ i : Fin rows.length, x<N.banks.charges ∨
          N.banks.nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤x := by
  intro W p A ss N rows x hx
  have space:=Parameters.node_publication_arena B u rem low stride cells shape off tariff hu levels factor half depth
  have heapRoom : (finish A.K ss A.cursor).heap≤TickWorkspace.base u 22+TickWorkspace.stride u :=
    cursor_heap_end B hu levels factor half depth A.K A.cursor
  have lowEnd : TickWorkspace.base u 22+TickWorkspace.stride u≤N.banks.current :=
    TickWorkspace.apart (by decide : 22<40)
  have ctl : N.counter=N.banks.current+3 := rfl
  have ch : N.banks.current<N.banks.charges := space.current
  have head : N.counter<N.headerBase := space.counter
  have lend : N.headerBase+16*rows.length≤N.banks.charges := space.header
  have bst : N.banks.charges+TickWorkspace.stride u≤N.banks.nodes :=
    TickWorkspace.apart (by decide : 43<44)
  have highStart : N.banks.nodes+TickWorkspace.stride u≤A.initialRecords :=
    TickWorkspace.apart (by decide : 44<49)
  have strideBound : 2^(u^10-u^4)≤TickWorkspace.stride u :=
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le (u^10) (u^4))).trans
      (Nat.le_self_pow (by decide : 4≠0) _)
  have counts:=node_count_space B p hu levels factor half depth (by rfl)
  have ends (i : Fin rows.length) :
      N.banks.nodes+8*((rows.get i).actual.first+(rows.get i).actual.count)≤A.initialRecords := by
    have n := counts.1 (rows.get i) (List.get_mem rows i)
    exact (Nat.add_le_add_left (n.trans strideBound) _).trans highStart
  have endCharge (i : Fin rows.length) :=
    (space.span (rows.get i) (List.get_mem rows i)).1
  rcases hx with before|⟨above,under⟩
  · have xctl : x<N.banks.current := (before.trans_le heapRoom).trans_le lowEnd
    refine ⟨?_,⟨by omega,by omega,Or.inl (by omega),?_⟩,fun _=>Or.inl (by omega)⟩
    · have t:=space.nodeEnd
      change N.banks.nodes+8*((rows.map (fun z=>z.actual.count)).sum)<2^W at t
      omega
    · intro i
      exact ⟨by omega,by omega,Or.inl (by omega),Or.inl (by omega)⟩
  · have degree : 2^B.exponent 0≤u := by unfold directoryCap at fixed;omega
    have atDepth : p.axes≤u^10+2*u^6 := by change (B.repeat (u^8)).charge+rem≤_;omega
    have endFit : A.metadataEnd<2^W := (p.initial_space (2^B.exponent 0) hu degree atDepth).records.endFit
    refine ⟨under.trans endFit,⟨by omega,by omega,Or.inr (by omega),?_⟩,fun i=>Or.inr ((ends i).trans above)⟩
    intro i
    have cen:=endCharge i
    have nen:=ends i
    exact ⟨by omega,by omega,Or.inr (by omega),Or.inr (by omega)⟩

theorem seed_le_maxRows (f : Stage→ℕ) (seed : ℕ) (steps : List Stage) : seed≤ maxRows f seed steps := by
  induction steps with
  | nil => exact le_rfl
  | cons st ss ih => exact ih.trans (le_max_right _ _)

theorem stage_le_maxRows (f : Stage→ℕ) (seed : ℕ) (steps : List Stage) (t : Stage) (ht : t∈steps) :
    f t≤ maxRows f seed steps := by
  induction steps with
  | nil => simp at ht
  | cons s ss ih =>
    rcases List.mem_cons.mp ht with eq|mem
    · subst t;exact le_max_left _ _
    · exact (ih mem).trans (le_max_right _ _)

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
