import OAI.ThreeFlat.RAM.HistoryStageJoinTariff
import OAI.ThreeFlat.RAM.HistoryStageArmResources
import OAI.ThreeFlat.Diagonal.HistoryStageCharges

namespace OAI
/-! # Instruction costs of a selected stage and its ancestors -/

namespace ThreeFlat.RAM.HistoryStageBody.StageRun
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr HistoryBoundedBody HistoryStageRoot
open HistoryStageBody.Physical HistoryPartyBatchExec
open scoped BigOperators Fin.CommRing
noncomputable section

/-- The actual inherited addresses copied by the stage's endpoint sweep. -/
def extWords {W : ℕ} (X : StageRun W) :=
  HistoryStageRoot.prefix X.inputs X.childRaw (childCount X.inputs X.childRaw) Result.extCount

/-- One fixed coefficient for a stage schema. The numerical addresses and the
length of the complete history never enter it. -/
def rootRate (template : HistoryGatherBody.Layout) (cap : ℕ) :=
  1024*(cap+2)*(1+rootResources template cap)

private theorem bank_extent {W cap : ℕ} (t : Input) (b : Bank) (m : Memory W)
    (n : childCount t (numeric m)≤cap) : bankSize t (numeric m) b≤7*(cap+1) := by
  cases b <;> simp only [bankSize,Bank.width,rowCount] <;> omega

open private HistoryStageBody.Physical.root_cache_cost from
  OAI.ThreeFlat.RAM.HistoryStageArmResources
open private HistoryStageBody.Physical.readyResources_eq HistoryStageBody.Physical.ready_empty_rows from
  OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources

private theorem component_rates (header cache ready join : ℕ) (scan : Bank → ℕ) :
    let total := 1+(11+4*header+scan .hub+scan .link+scan .mapArgs+scan .extArgs+
      scan .extCommand+(11+4*cache)+ready+join+scan .result)
    (∀ b, scan b ≤ total) ∧ 2*header+4 ≤ total ∧ 2*cache+4 ≤ total ∧
      ready ≤ total ∧ 1+join ≤ total := by
  dsimp only
  refine ⟨?_, by omega, by omega, by omega, by omega⟩
  intro b
  cases b <;> omega

private theorem instruction_rate {work bound : ℕ} (fit : work ≤ bound) :
    2*work+4 ≤ 18+4*bound := by omega

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1200000 in
/-- All intermediate bank sizes come from the installed header and its
native child cap. The only variable work is copying inherited addresses,
ordered child pins and four-word cell rows. -/
theorem typed_cost_le {W n p h : ℕ} {F : Type*} {arity : Fin n→ℕ} (X : StageRun W)
    (template : HistoryGatherBody.Layout) (mode : X.layout.mode=template.mode)
    (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin n→HistoryJoinScan.Header ℕ)
    (head : X.Header) (source : Build.Source X.compiled (Tape.tape N wire id q)) :
    let ops : List (HistoryReadyTape.Job W) := Tape.tape N wire id q
    X.prepareCost+X.compiled.ticks ops+writeCost X.layout X.cap X.inputs .result (X.compiled.output ops) ≤
      rootRate template X.cap*(1+X.extWords+((List.finRange n).map (fun i=>arity i+4*(N i).cells)).sum) := by
  intro ops
  let K:=1+rootResources template X.cap
  let words:=((List.finRange n).map (fun i=>arity i+4*(N i).cells)).sum
  let units:=(X.cap+2)*(1+X.extWords+words)
  let price:=units*K
  have kp : 0<K := by dsimp only [K];omega
  have cu : X.cap+2≤units := Nat.le_mul_of_pos_right _ (by omega)
  have wu : 1+X.extWords+words≤units := Nat.le_mul_of_pos_left _ (by omega)
  have pu : units≤price := Nat.le_mul_of_pos_right _ kp
  have pk : K≤price := Nat.le_mul_of_pos_left _ (by omega)
  have count := source.count
  rw [Tape.tape_length] at count
  have cap:=source.cap
  change childCount X.inputs X.childRaw+1≤X.cap+1 at cap
  change 2*n=2*(childCount X.inputs X.childRaw+1) at count
  obtain ⟨scanRate, headerLimit, cacheLimit, readyLimit, joinLimit⟩ :=
    component_rates (joinHeader template X.cap 1).binds (cache (W:=1) template).binds
      readyResources (joinResources (X.cap+1)) (rootScanResources X.cap)
  have field (b : Bank) : 2*(fieldProgram X.layout X.cap W b).binds+4 ≤ K :=
    (instruction_rate (field_bound X.layout X.cap W b)).trans (scanRate b)
  have write {b : Bank} {m : Memory W} (rows : bankSize X.inputs (numeric m) b≤7*units) :
      writeCost X.layout X.cap X.inputs b m≤20*price := by
    have t := Nat.mul_le_mul rows (field b)
    change 13+bankSize X.inputs (numeric m) b*(2*(fieldProgram X.layout X.cap W b).binds+4)≤_
    have h : 7*units*K=7*price := by dsimp only [price];ring
    omega
  have inputWrite {b : Bank} {j : ℕ} {m : Memory W} (hb : BankInput X.layout X.cap X.inputs b j m) :=
    write ((bank_extent X.inputs b m hb.children).trans (Nat.mul_le_mul_left 7 (by omega)))
  have h0:=inputWrite head.hub
  have h1:=inputWrite head.children
  have h2:=inputWrite head.maps
  have h3:=inputWrite head.tuples
  have h4:=inputWrite head.commands
  have last : writeCost X.layout X.cap X.inputs .result (X.compiled.output ops)≤20*price := by
    apply write
    change 6*1≤7*units
    omega
  have headerRate : 2*(joinHeader X.layout X.cap W).binds+4≤K := by
    rw [joinHeader_work X.layout X.cap template W 1 mode]
    exact headerLimit
  have number : (fields (W:=W) X.layout X.cap).length ≤ 64 := by
    change 26 ≤ 64
    decide
  have boot : X.bootCost≤68*price := by
    have t:=Nat.mul_le_mul number headerRate
    dsimp only [bootCost]
    omega
  have cacheEq : (cache (W:=W) X.layout).binds=(cache (W:=1) template).binds :=
    HistoryStageBody.Physical.root_cache_cost W X.layout template
  have cacheRate : 2*(cache (W:=W) X.layout).binds+4≤K := by
    rw [cacheEq]
    exact cacheLimit
  have tapeRate : 2*(Tape.expr W).binds+4≤K := by
    have work : (Tape.expr W).binds ≤ HistorySelectedOps.tariff [] :=
      HistoryStageBody.Physical.ready_empty_rows W
    have within (n : ℕ) : 2*n+4 ≤ 30+4*n := by omega
    calc
      2*(Tape.expr W).binds+4 ≤ 2*HistorySelectedOps.tariff []+4 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 work) 4
      _ ≤ readyResources :=
        (within (HistorySelectedOps.tariff [])).trans_eq HistoryStageBody.Physical.readyResources_eq
      _ ≤ K := readyLimit
  have copy : X.copyCost≤26*price := by
    have t:=Nat.mul_le_mul (show X.extWords≤units by omega) tapeRate
    dsimp only [copyCost,endpointJobs]
    rw [Endpoints.tape_cost]
    change 6+19*childCount X.inputs X.childRaw+X.extWords*(2*(Tape.expr W).binds+4)≤_
    dsimp only [price] at t ⊢
    omega
  have compiled : X.compiled.ticks ops≤300*price := by
    have t:=X.compiled.typed_ticks_le N wire id q
    have rate : 1+joinResources X.compiled.cap≤K := by
      exact joinLimit
    have quantity : 1+X.compiled.hub.argc+n+words≤3*units := by
      change 1+(childCount X.inputs X.childRaw+1)+n+words≤_
      omega
    have pay:=Nat.mul_le_mul (Nat.mul_le_mul_left 100 rate) quantity
    have eq : 100*K*(3*units)=300*price := by dsimp only [price];ring
    exact t.trans (pay.trans_eq eq)
  have spend : X.prepareCost+X.compiled.ticks ops+writeCost X.layout X.cap X.inputs .result (X.compiled.output ops)
      ≤1024*price := by
    dsimp only [prepareCost]
    omega
  have priceEq : 1024*price = rootRate template X.cap*(1+X.extWords+words) := by
    change 1024*((X.cap+2)*(1+X.extWords+words)*K) = 1024*(X.cap+2)*K*(1+X.extWords+words)
    ac_rfl
  exact spend.trans_eq priceEq

section TypedStage
open Diagonal.HistoryContraction
variable {W : ℕ} {F Pins : Type*} [CommSemiring F] {S : Diagonal.HistoryContraction.Shape} {R : Rewrite S F} {b : Fin R.count}
    {old : Form S Pins} {newForm : Form (R.target b) Pins}

theorem tape_words_le_resources (D : Stage R b old newForm) (forest : Forest F old) (v : (R.target b).Site) :
    ((List.finRange (D.count v+1)).map fun i=>D.tapeArity forest v i+4*(D.tapeFactor forest v i).compile.cells).sum
      ≤4*(D.assemble forest v).resources := by
  rw [←Fin.sum_univ_def]
  simp only [Tree.compiled_rows,Finset.sum_add_distrib,←Finset.mul_sum]
  have rows : (∑ i,(D.tapeFactor forest v i).rows)=(D.assemble forest v).rows := rfl
  have maps : (∑ i,D.tapeArity forest v i)≤(D.assemble forest v).footprint.pins := by
    change _≤(∑ i,(D.tapeFactor forest v i).footprint.pins)+∑ i,D.tapeArity forest v i
    omega
  rw [rows,Tree.resources,Stage.treeWork]
  omega

/-- The extra endpoint term equals the sum of the true external widths of the
stage's actual children. Each child pointer is inspected at its real ordinal. -/
theorem extWords_ports (X : StageRun W) (L : PortLayout S Pins) (V : PortLayout (R.target b) Pins)
    (count : (R.target b).Site→ℕ) (order : ∀ v,Fin (count v)≃{j // R.owner b j=v}) (v : (R.target b).Site)
    (ports : Ports L V count order v X.inputs X.childRaw) :
    X.extWords=∑ i:Fin (count v),L.ext (order v i).val := by
  unfold extWords
  rw [ports.degree]
  simpa using prefix_value Result.extCount (fun i=>L.ext (order v i).val) ports.childExt (count v) le_rfl

/-- The scalar charge is for the executed native stage and its actual ordered
factor records. It applies to the very output used by join_stage. -/
theorem stage_cost_le (X : StageRun W) (template : HistoryGatherBody.Layout) (mode : X.layout.mode=template.mode)
    (D : Stage R b old newForm) (forest : Forest F old) (v : (R.target b).Site)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin (D.count v+1)→HistoryJoinScan.Header ℕ)
    (head : X.Header)
    (source : Build.Source X.compiled (Tape.tape (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q)) :
    let ops:=Tape.tape (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q
    X.prepareCost+X.compiled.ticks ops+
      writeCost X.layout X.cap X.inputs .result (X.compiled.output ops) ≤
      rootRate template X.cap*(1+X.extWords+4*(D.assemble forest v).resources) := by
  apply (X.typed_cost_le template mode (fun i=>(D.tapeFactor forest v i).compile)
    (D.tapePin forest v) id q head source).trans
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (tape_words_le_resources D forest v) _)

/-- Every surviving external pin belongs to the corresponding old factor's
arity and therefore already occurs in the assembled tape's map footprint. -/
theorem extWords_le_resources (X : StageRun W) (L : PortLayout S Pins) (V : PortLayout (R.target b) Pins)
    (D : Stage R b L.form newForm) (forest : Forest F L.form) (v : (R.target b).Site)
    (ports : Ports L V D.count D.child v X.inputs X.childRaw) :
    X.extWords≤(D.assemble forest v).resources := by
  rw [X.extWords_ports L V D.count D.child v ports,Tree.resources,D.pinWords_assemble]
  have charge := Finset.sum_le_sum (s:=Finset.univ) fun (i : Fin (D.count v)) _=>
    show L.ext (D.child v i).val ≤ (forest (D.child v i).val).footprint.pins+L.form.width (D.child v i).val by
      change _≤_+(L.ext _+L.halfBits _)
      omega
  omega

theorem stage_cost_from_ports (X : StageRun W) (template : HistoryGatherBody.Layout)
    (mode : X.layout.mode=template.mode) (L : PortLayout S Pins) (V : PortLayout (R.target b) Pins)
    (D : Stage R b L.form newForm) (forest : Forest F L.form) (v : (R.target b).Site)
    (ports : Ports L V D.count D.child v X.inputs X.childRaw)
    (id : ((Fin 3→Bool)→F)→ℕ) (q : Fin (D.count v+1)→HistoryJoinScan.Header ℕ)
    (head : X.Header)
    (source : Build.Source X.compiled (Tape.tape (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q)) :
    let ops:=Tape.tape (fun i=>(D.tapeFactor forest v i).compile) (D.tapePin forest v) id q
    X.prepareCost+X.compiled.ticks ops+writeCost X.layout X.cap X.inputs .result (X.compiled.output ops) ≤
      (6*rootRate template X.cap)*(D.assemble forest v).resources := by
  have e:=X.extWords_le_resources L V D forest v ports
  have pos : 1≤(D.assemble forest v).resources := by
    have n:=(D.assemble forest v).nodes_pos
    dsimp only [Tree.resources,Stage.treeWork]
    omega
  have bound : 1+X.extWords+4*(D.assemble forest v).resources≤6*(D.assemble forest v).resources := by omega
  exact (X.stage_cost_le template mode D forest v id q head source).trans
    ((Nat.mul_le_mul_left _ bound).trans_eq (by ring))

/-- Charge the genuine earlier subtree traversals at the next stage. The rate
accumulates additively with depth because each child occurs in just one owner
fiber. -/
theorem stage_ancestor_cost (D : Stage R b old newForm) (forest : Forest F old) (v : (R.target b).Site)
    (prior : S.Site→ℕ) (before now ticks : ℕ)
    (earlier : ∀ i, prior (D.child v i).val≤before*(forest (D.child v i).val).resources)
    (localTicks : ticks≤now*(D.assemble forest v).resources) :
    ticks+∑ i,prior (D.child v i).val≤(before+now)*(D.assemble forest v).resources := by
  have childUnits : (∑ i,(forest (D.child v i).val).resources)≤(D.assemble forest v).resources := by
    rw [D.resources_assemble]
    simp only [Finset.sum_add_distrib]
    omega
  have accumulated:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>earlier i
  rw [←Finset.mul_sum] at accumulated
  have kids:=accumulated.trans (Nat.mul_le_mul_left before childUnits)
  rw [Nat.add_mul]
  omega

/-- Pointwise induction on genuine stage ownership. Local resources and
old boundary widths add at most two units per level. Their repeated native
copying gives a quadratic factor in the number of stages. -/
theorem stage_totals (D : Stage R b old newForm) (forest : Forest F old) (v : (R.target b).Site)
    (prev native : S.Site→ℕ) (fresh depth unit rate kernel join : ℕ)
    (oldTree : ∀ i,(forest (D.child v i).val).resources≤((2*depth+1)*unit)*prev (D.child v i).val)
    (oldWidth : ∀ i,old.width (D.child v i).val≤unit*prev (D.child v i).val)
    (oldNative : ∀ i,native (D.child v i).val≤(10*(depth+1)^2*rate*unit)*prev (D.child v i).val)
    (localTree : D.freshResources v≤unit*(fresh+∑ i,prev (D.child v i).val))
    (kernelTicks : kernel≤rate*(unit*(fresh+∑ i,prev (D.child v i).val)+(D.assemble forest v).resources))
    (joinTicks : join≤rate*(D.assemble forest v).resources) :
    let charge:=fresh+∑ i,prev (D.child v i).val
    (D.assemble forest v).resources≤((2*(depth+1)+1)*unit)*charge ∧
      kernel+join+(∑ i,native (D.child v i).val)≤(10*(depth+2)^2*rate*unit)*charge := by
  intro charge
  let oldMass:=∑ i,prev (D.child v i).val
  have enough : oldMass≤charge := Nat.le_add_left _ _
  have treeSum := Finset.sum_le_sum (s:=Finset.univ) fun i _=>oldTree i
  have widthSum := Finset.sum_le_sum (s:=Finset.univ) fun i _=>oldWidth i
  rw [←Finset.mul_sum] at treeSum widthSum
  have fromChild := Nat.add_le_add treeSum widthSum
  have a:=Nat.mul_le_mul_left ((2*depth+1)*unit) enough
  have b₀:=Nat.mul_le_mul_left unit enough
  have tree : (D.assemble forest v).resources≤((2*(depth+1)+1)*unit)*charge := by
    rw [D.resources_assemble]
    have p : ((2*(depth+1)+1)*unit)*charge=
        unit*charge+(((2*depth+1)*unit)*charge+unit*charge) := by ring
    rw [p, Finset.sum_add_distrib]
    exact Nat.add_le_add localTree (fromChild.trans (Nat.add_le_add a b₀))
  refine ⟨tree,?_⟩
  have past:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>oldNative i
  rw [←Finset.mul_sum] at past
  have earlier:=past.trans (Nat.mul_le_mul_left _ enough)
  have j:=joinTicks.trans (Nat.mul_le_mul_left rate tree)
  have k:=kernelTicks.trans (Nat.mul_le_mul_left rate (Nat.add_le_add_left tree (unit*charge)))
  apply (Nat.add_le_add (Nat.add_le_add k j) earlier).trans
  have scalar : 1+2*(2*(depth+1)+1)+10*(depth+1)^2≤10*(depth+2)^2 := by nlinarith
  calc
    _ = (1+2*(2*(depth+1)+1)+10*(depth+1)^2)*(rate*unit*charge) := by ring
    _ ≤ (10*(depth+2)^2)*(rate*unit*charge) := Nat.mul_le_mul_right _ scalar
    _ = _ := by ring


end TypedStage

/-- At most one native word width of chronological levels and cubic local
compactor cost give a fixed fifth-degree tariff in the word width. -/
theorem stage_rate_five {depth W rate unit C : ℕ} (levels : depth≤W) (cubic : unit≤C*(W+1)^3) :
    10*(depth+2)^2*rate*unit≤(40*rate*C)*(W+1)^5 := by
  have d : depth+2≤2*(W+1) := by omega
  calc
    _ ≤ 10*(2*(W+1))^2*rate*(C*(W+1)^3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left d _))) cubic
    _ = _ := by ring


end
end ThreeFlat.RAM.HistoryStageBody.StageRun

end OAI
