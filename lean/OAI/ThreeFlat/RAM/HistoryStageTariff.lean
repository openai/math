import OAI.ThreeFlat.RAM.HistoryStageRunTariff
import OAI.ThreeFlat.RAM.HistoryStageResources

namespace OAI
/-! # Bounds for the stage tariff, tree scratch space, and initial receiver -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.PhysicalStage
open private familiesFrom_schema from OAI.ThreeFlat.RAM.HistoryStageResources
open private root_cache_cost from OAI.ThreeFlat.RAM.HistoryStageArmResources

/-- A compile-time constant shared by all occurrences of the stage schema. -/
noncomputable def familyRootRate (f : Family) := StageRun.rootRate (layout 0 ⟨0,0,0,0,0,0⟩ f) f.childBound

noncomputable def blockRootRate {F : Type} [Field F] [Fintype F] (B : Block F) :=
  1+((families B 0 0).map familyRootRate).sum

private theorem member_sum (n : ℕ) (xs : List ℕ) (member : n∈xs) : n≤xs.sum := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with h|h
    · simp [h]
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem block_root_template {F : Type} [Field F] [Fintype F] (B : Block F) (start height : ℕ)
    (f : Family) (member : f∈families B start height) :
    ∃ g∈families B 0 0, f.mode=g.mode ∧ f.childBound=g.childBound ∧ familyRootRate g≤blockRootRate B := by
  have schemas : (families B start height).map Family.schema=(families B 0 0).map Family.schema :=
    familiesFrom_schema _ _ _
  have hf : f.schema∈(families B 0 0).map Family.schema := schemas ▸ List.mem_map_of_mem member
  obtain ⟨g,hg,eq⟩:=List.mem_map.mp hf
  have cap:=member_sum _ _ (List.mem_map_of_mem (f:=familyRootRate) hg)
  have project {α : Type} (field : Family→α) : field f.schema=field g.schema :=
    congrArg field eq.symm
  exact ⟨g,hg,project Family.mode,project Family.childBound,cap.trans (Nat.le_add_left _ 1)⟩

section
attribute [local irreducible] rootScanResources readyResources joinResources
  HistoryStageBody.joinHeader HistoryStageBody.cache

private theorem rootRate_mode (A B : HistoryGatherBody.Layout) (cap : ℕ) (mode : A.mode=B.mode) :
    StageRun.rootRate A cap=StageRun.rootRate B cap := by
  simp only [StageRun.rootRate,rootResources,HistoryStageBody.joinHeader_work A cap B 1 1 mode,
    root_cache_cost 1 A B]
end

/-- Uniform pointwise tariff for the literal physical stage selected from
the finite codebook, even when its addresses depend on the current age. -/
theorem block_root_rate {F : Type} [Field F] [Fintype F] (B : Block F) (start height u : ℕ)
    (archive : Archive) (f : Family) (member : f∈families B start height) :
    StageRun.rootRate (layout u archive f) f.childBound≤blockRootRate B := by
  obtain ⟨g,_,mode,cap,bound⟩:=block_root_template B start height f member
  have count := congrArg (StageRun.rootRate (layout u archive f)) cap
  have price : StageRun.rootRate (layout u archive f) f.childBound=familyRootRate g :=
    count.trans (rootRate_mode (layout u archive f) (layout 0 ⟨0,0,0,0,0,0⟩ g) g.childBound mode)
  exact price.le.trans bound


end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.Diagonal.HistoryContraction.Tree
open scoped Classical BigOperators

theorem child_resources {F : Type*} {p : ℕ} (h c : ℕ) (a : Fin c→ℕ) (wire : ∀ i,Fin (a i)→BitSource h p)
    (child : ∀ i,Tree F (a i)) (i : Fin c) :
    (child i).resources+a i≤(Tree.join h c a wire child).resources := by
  have inSum (f : Fin c→ℕ) : f i≤∑ j,f j:=Finset.single_le_sum (fun j _=>Nat.zero_le (f j)) (Finset.mem_univ i)
  have b:=inSum (fun j=>(child j).bits)
  have r:=inSum (fun j=>(child j).rows)
  have n:=inSum (fun j=>(child j).nodes)
  have p:=inSum (fun j=>(child j).footprint.pins)
  have ar:=inSum a
  simp only [resources,Stage.treeWork,bits,rows,nodes,footprint]
  omega

/-- Scratch sizes for every embedded private party and combiner tape. -/
def ChildrenFit {F : Type*} (V : ℕ) : {p : ℕ} → Tree F p → Prop
  | _,.atom _=>True
  | _,.join _ _ a _ child=>∀ i,8*(child i).rows≤V ∧ (child i).bits+a i≤V ∧ ChildrenFit V (child i)

theorem children_fit {F : Type*} {p V : ℕ} (T : Tree F p) (size : 8*T.resources≤V) : ChildrenFit V T := by
  induction T with
  | atom _=>trivial
  | join h c a wire child ih=>
    intro i
    have element:=child_resources h c a wire child i
    have word : (child i).bits≤(child i).resources:=by unfold resources Stage.treeWork;omega
    have row : (child i).rows≤(child i).resources:=by unfold resources Stage.treeWork;omega
    exact ⟨by omega,by omega,ih i (by omega)⟩


end ThreeFlat.Diagonal.HistoryContraction.Tree

namespace ThreeFlat.RAM.HistoryStageBody.StageRun
open Computability.VPVNP.BurstRAM Diagonal.HistoryContraction HistoryStageRoot
open scoped BigOperators

/-- The actual single-site scheduler cap leaves room for eight full streams in
one V-word slab. Here V is 2^(u^10), the physical S12 allocation. -/
theorem site_peak_slab {u : ℕ} (age : 2≤u) : 8*2^((3*u^10+4)/5)≤2^(u^10) := by
  have large : 2^10≤u^10:=Nat.pow_le_pow_left age 10
  norm_num at large
  have power : 3+(3*u^10+4)/5≤u^10:=by omega
  calc
    _ = 2^(3+(3*u^10+4)/5) := by rw [pow_add];norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by decide) power

/-- A typed node's own stream, private variable namespace, and each embedded
party/batch tape are bounded by its real charge at this level. -/
theorem tree_scratch_at_peak {u unitWork charge depth unit rate ext half : ℕ} {F : Type*}
    (age : 2≤u) (T : Tree F (ext+half)) (resources : T.resources≤((2*depth+1)*unit)*charge)
    (width : ext+half≤unit*charge) (rateLive : 1≤rate)
    (tariff : 10*(depth+1)^2*rate*unit≤unitWork) (peak : unitWork*charge≤2^((3*u^10+4)/5)) :
    8*T.rows≤2^(u^10) ∧ T.bits+ext+half≤2^(u^10) ∧ T.ChildrenFit (2^(u^10)) ∧
      8*T.resources≤2^(u^10) := by
  have scaffold : 2*depth+1≤10*(depth+1)^2:=by nlinarith
  have scaled : (2*depth+1)*unit≤unitWork:=by
    apply Nat.le_trans _ tariff
    have scaledRate : 10*(depth+1)^2≤10*(depth+1)^2*rate :=
      Nat.le_mul_of_pos_right _ rateLive
    exact Nat.mul_le_mul_right unit (scaffold.trans scaledRate)
  have base : unit≤unitWork:=by
    have p:=Nat.mul_le_mul_right unit (show 1≤2*depth+1 by omega)
    simpa using p.trans scaled
  have clip:=resources.trans ((Nat.mul_le_mul_right charge scaled).trans peak)
  have arity:=width.trans ((Nat.mul_le_mul_right charge base).trans peak)
  have rows : T.rows≤T.resources:=by unfold Tree.resources Stage.treeWork;omega
  have bits : T.bits≤T.resources:=by unfold Tree.resources Stage.treeWork;omega
  have bank:=site_peak_slab age
  exact ⟨by omega,by omega,T.children_fit (by omega),by omega⟩

/-- Direct source for the header's child-endpoint-prefix bound, using the
actual captured ports in the installed stage. -/
theorem header_prefix_scratch {W u : ℕ} {F Pins : Type*} [CommSemiring F]
    {S : Diagonal.HistoryContraction.Shape} {R : Rewrite S F} {b : Fin R.count} {newForm : Form (R.target b) Pins}
    (X : StageRun W) (L : PortLayout S Pins) (V : PortLayout (R.target b) Pins)
    (D : Stage R b L.form newForm) (forest : Forest F L.form) (v : (R.target b).Site)
    (ports : Ports L V D.count D.child v X.inputs X.childRaw)
    (scratch : 8*(D.assemble forest v).resources≤2^(u^10)) :
    HistoryStageRoot.prefix X.inputs X.childRaw (childCount X.inputs X.childRaw) Result.extCount≤2^(u^10) := by
  have raw:=X.extWords_le_resources L V D forest v ports
  change X.extWords≤_
  omega


end ThreeFlat.RAM.HistoryStageBody.StageRun

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.PhysicalStage
open private familiesFrom_schema from OAI.ThreeFlat.RAM.HistoryStageResources

/-- Space reserved for fixed party descriptors and old-child counters. -/
def staticStageWords (f : Family) := f.childBound+(2*(f.parties+2)*8+5)*32+8
noncomputable def blockStageWords {F : Type} [Field F] [Fintype F] (B : Block F) :=
  ((families B 0 0).map staticStageWords).sum

theorem header_static_at_scale {F : Type} [Field F] [Fintype F] (B : Block F) (start height u : ℕ)
    (f : Family) (member : f∈families B start height) (_age : 1≤u) (fixed : blockStageWords B≤u) :
    f.childBound≤2^(u^10) ∧ (2*(f.parties+2)*8+5)*32+8≤2^(u^10) := by
  have schemas : (families B start height).map Family.schema=(families B 0 0).map Family.schema:=
    familiesFrom_schema _ _ _
  have hf : f.schema∈(families B 0 0).map Family.schema:=schemas ▸ List.mem_map_of_mem member
  obtain ⟨g,hg,eq⟩:=List.mem_map.mp hf
  have project {α : Type} (field : Family → α) : field g.schema = field f.schema :=
    congrArg field eq
  have sameC : g.childBound = f.childBound := project Family.childBound
  have sameP : g.parties = f.parties := project Family.parties
  have cap:=member_sum _ _ (List.mem_map_of_mem (f:=staticStageWords) hg)
  change staticStageWords g≤blockStageWords B at cap
  simp only [staticStageWords,sameC,sameP] at cap
  have xe : u≤u^10:=Nat.le_self_pow (by decide) u
  have big:=Nat.lt_two_pow_self (n:=u^10)
  omega


end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM

private def leafRate (cap : ℕ) := 400063 + 12*(2*cap+4)

private theorem leafRate_eq (cap : ℕ) : 400063 + 12*(2*cap+4) = leafRate cap := rfl

/-- Real per-unit cost of executing the raw-image trace leaf, including all
866 virtual accesses for each original H lookup. -/
noncomputable def leafRuntimeRate := leafRate (HistorySelectedOps.tariff [] + 3*rawLeafBinds)

attribute [local irreducible] HistorySelectedOps.tariff rawLeafBinds HistoryInitialSeed.formula
  HistoryInitialSeed.rows

private theorem leafRuntimeRate_eq :
    400063 + 12*(2*(HistorySelectedOps.tariff [] + 3*rawLeafBinds)+4) = leafRuntimeRate := by
  unfold leafRuntimeRate
  exact leafRate_eq (HistorySelectedOps.tariff [] + 3*rawLeafBinds)

private theorem leaf_price_bound (initial rows pins binds amount cap rate : ℕ) (setup : initial ≤ 400000)
    (positive : 1 ≤ amount) (rowBound : rows ≤ amount) (pinBound : pins ≤ 2*amount) (bindBound : binds ≤ cap)
    (price : 400063 + 12*(2*cap+4) = rate) :
    initial + (63 + (4*rows + pins + 6)*(2*binds + 4)) ≤ rate*amount := by
  have words : 4*rows + pins + 6 ≤ 12*amount := by omega
  have ops := Nat.mul_le_mul words (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bindBound) 4)
  have fixed : initial + 63 ≤ 400063*amount := by
    calc
      initial + 63 ≤ 400063 := by omega
      _ = 400063*1 := by simp
      _ ≤ 400063*amount := Nat.mul_le_mul_left 400063 positive
  calc
    _ = (initial + 63) + (4*rows + pins + 6)*(2*binds + 4) := by omega
    _ ≤ 400063*amount + 12*amount*(2*cap + 4) := Nat.add_le_add fixed ops
    _ = (400063 + 12*(2*cap+4))*amount := by ring
    _ = rate*amount := congrArg (fun n => n*amount) price

theorem leaf_runtime_price {W : ℕ} (A : HistoryInitialSeed.Layout) (z : HistoryInitialSeed.Site)
    (amount : ℕ) (positive : 1≤amount) (rows : z.rows A≤amount) (pins : z.extPins≤2*amount) :
    4+42*(2*(HistoryInitialSeed.formula A).work+4)+
      (63+(4*z.rows A+z.extPins+6)*(2*(HistoryInitialSeed.rows W A).binds+4))≤leafRuntimeRate*amount :=
  leaf_price_bound (4+42*(2*(HistoryInitialSeed.formula A).work+4)) (z.rows A) z.extPins
    (HistoryInitialSeed.rows W A).binds amount (HistorySelectedOps.tariff []+3*rawLeafBinds) leafRuntimeRate
    (HistoryInitialSeed.seed_budget A) positive rows pins (initial_rows_size (W:=W) A) leafRuntimeRate_eq


end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
