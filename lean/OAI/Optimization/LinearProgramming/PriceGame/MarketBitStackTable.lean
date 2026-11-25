import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStack
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap
import Mathlib.Data.Nat.Size

/-! A uniform serialized Bellman computation. Graph rows contain a terminal integer payoff and
a list of indexed arcs with an integer cost and an arc identifier. A returned item contains its
score, length, and forward list of arc identifiers. All neighbor lookups are bit-stack list
operations. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Table

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Item := Key × List ℕ
abbrev Arc := (ℕ × ℤ) × ℕ
abbrev Row := ℤ × List Arc
abbrev Graph := List Row

def routeCode := listCode Nat.bits
def itemCode := prodCode keyCode routeCode
def arcCode := prodCode (prodCode Nat.bits intCode) Nat.bits
def rowCode := prodCode intCode (listCode arcCode)
def graphCode := listCode rowCode
def valuesCode := listCode itemCode

def zeroItem : Item := ((0,0),[])
def zeroArc : Arc := ((0,0),0)
def zeroRow : Row := (0,[])

def start (row : Row) : Item := ((row.1,0),[])

def neighbor (values : List Item) (edge : Arc) : Item :=
  (values.drop edge.1.1).headD zeroItem

def extend (z : List Item × Arc) : Item :=
  let prev := neighbor z.1 z.2
  (nextKey (prev.1, z.2.1.2), z.2.2 :: prev.2)

def rowResult (z : List Item × Row) : Item :=
  (z.2.2.map (fun e => extend (z.1,e))).foldl (fun best cand => winner (best,cand)) (start z.2)

def layer (z : Graph × List Item) := z.1.map (fun row => rowResult (z.2,row))

def update (z : Graph × List Item) := (z.1, layer z)

noncomputable def startProgram : Procedure rowCode itemCode start := by
  let val := first intCode (listCode arcCode)
  let len := constant rowCode intCode (0 : ℤ)
  let empty := constant rowCode routeCode ([] : List ℕ)
  exact ((val.pair len).pair empty).congrFun (fun _ => rfl)

noncomputable def extendProgram : Procedure (prodCode valuesCode arcCode) itemCode extend := by
  let old := first valuesCode arcCode
  let edge := second valuesCode arcCode
  let data := (first (prodCode Nat.bits intCode) Nat.bits).comp edge
  let dest := (first Nat.bits intCode).comp data
  let weight := (second Nat.bits intCode).comp data
  let ident := (second (prodCode Nat.bits intCode) Nat.bits).comp edge
  let prev := (listGet itemCode zeroItem).comp (dest.pair old)
  let key := (first keyCode routeCode).comp prev
  let path := (second keyCode routeCode).comp prev
  exact ((nextKeyProgram.comp (key.pair weight)).pair ((listCons Nat.bits).comp (ident.pair path))).congrFun
    (fun _ => rfl)

/-- The program looks up each listed destination in the serialized preceding table, copies its
route and prepends the current arc identifier. -/
noncomputable def rowProgram : Procedure (prodCode valuesCode rowCode) itemCode rowResult := by
  let old := first valuesCode rowCode
  let row := second valuesCode rowCode
  let edges := (second intCode (listCode arcCode)).comp row
  let candidates := (mapWithContext zeroArc zeroItem extendProgram).comp (edges.pair old)
  let firstItem := startProgram.comp row
  exact ((foldWinnerProgram routeCode []).comp (candidates.pair firstItem)).congrFun (fun _ => rfl)

noncomputable def layerProgram : Procedure (prodCode graphCode valuesCode) valuesCode layer :=
  (mapWithContext zeroRow zeroItem rowProgram).congrFun (fun _ => rfl)

noncomputable def updateProgram : Procedure (prodCode graphCode valuesCode) (prodCode graphCode valuesCode)
    update := ((first graphCode valuesCode).pair layerProgram).congrFun (fun _ => rfl)

noncomputable def initialProgram : Procedure graphCode valuesCode (List.map start) :=
  listMap zeroRow zeroItem startProgram

/-- Every prefix of the winner fold retains either its seed or one of the candidates. -/
private theorem winner_source (xs : List Item) (init : Item) :
    xs.foldl (fun a b => winner (a,b)) init = init ∨ xs.foldl (fun a b => winner (a,b)) init ∈ xs := by
  induction xs generalizing init with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    rcases ih (winner (init,a)) with hs | hs
    · simp only [List.foldl_cons, hs]
      unfold winner
      split <;> simp
    · exact Or.inr (List.mem_cons_of_mem a hs)

private theorem head_mem_or_default (xs : List Item) (i : ℕ) :
    (xs.drop i).headD zeroItem = zeroItem ∨ (xs.drop i).headD zeroItem ∈ xs := by
  have hdrop := List.drop_sublist i xs
  cases h : xs.drop i with
  | nil => simp
  | cons a tail =>
    exact Or.inr (hdrop.subset (a := a) (by simp [h]))

private theorem intCode_length (z : ℤ) : (intCode z).length = z.natAbs.size + 3 := by
  simp [intCode, intData, prodCode, pairBits_length, boolCode, Nat.size_eq_bits_len]
  omega

private theorem intCode_add_le (a b : ℤ) :
    (intCode (a+b)).length ≤ (intCode a).length+(intCode b).length := by
  simp only [intCode_length]
  have h := (Nat.size_le_size (Int.natAbs_add_le a b))
  have ha : a.natAbs < 2^(a.natAbs.size+b.natAbs.size) :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b.natAbs < 2^(a.natAbs.size+b.natAbs.size) :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : (a.natAbs+b.natAbs).size ≤ a.natAbs.size + b.natAbs.size + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    omega
  omega

private theorem intCode_zero_length : (intCode 0).length = 3 := by decide
private theorem intCode_one_length : (intCode 1).length = 4 := by decide
private theorem zeroItem_length : (itemCode zeroItem).length = 22 := by decide

private theorem item_length (x : Item) :
    (itemCode x).length = 4*(intCode x.1.1).length+2*(intCode x.1.2).length+(routeCode x.2).length+3 := by
  simp [itemCode, keyCode, prodCode, pairBits_length]
  omega

private theorem start_length_le (row : Row) :
    (itemCode (start row)).length ≤ 4*(rowCode row).length+16 := by
  rw [item_length]
  simp only [start, rowCode, routeCode, prodCode, pairBits_length, listCode, List.length_cons,
    List.length_nil, intCode_zero_length]
  omega

/-- One update extends the preceding item by at most four times the arc encoding length plus
twelve bits. -/
private theorem extend_length_le (values : List Item) (edge : Arc) :
    (itemCode (extend (values,edge))).length ≤
      (itemCode (neighbor values edge)).length+4*(arcCode edge).length+12 := by
  let q := neighbor values edge
  have hscore := intCode_add_le q.1.1 edge.1.2
  have hlen := intCode_add_le q.1.2 1
  rw [intCode_one_length] at hlen
  rw [item_length, item_length]
  change 4*(intCode (q.1.1+edge.1.2)).length+2*(intCode (q.1.2+1)).length+
    (listCode Nat.bits (edge.2::q.2)).length+3 ≤ _
  rw [listCode_length_cons]
  simp only [arcCode, prodCode, pairBits_length]
  change _ ≤ 4*(intCode q.1.1).length+2*(intCode q.1.2).length+
    (listCode Nat.bits q.2).length+3+4*_+12
  omega


private theorem layer_item_bound (graph : Graph) (previous : List Item) {U : ℕ} (hu : 22 ≤ U)
    (hprev : ∀ x ∈ previous, (itemCode x).length ≤ U) :
    ∀ y ∈ layer (graph,previous), (itemCode y).length ≤ U+4*(graphCode graph).length+40 := by
  intro y hy
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hy
  change row ∈ graph at hrow
  have hr := code_le_of_mem rowCode hrow
  have hs := start_length_le row
  have hs' := winner_source
    (row.2.map fun e => extend (previous,e)) (start row)
  change (itemCode ((row.2.map (fun e => extend (previous,e))).foldl
    (fun best cand => winner (best,cand)) (start row))).length ≤ _
  rcases hs' with hz | hz
  · rw [hz]
    change _ ≤ U+4*(listCode rowCode graph).length+40
    omega
  · obtain ⟨e, he, hz⟩ := List.mem_map.mp hz
    rw [← hz]
    have hc := code_le_of_mem arcCode he
    have hrowArc : (listCode arcCode row.2).length ≤ (rowCode row).length := by
      simp only [rowCode,prodCode,pairBits_length]
      omega
    have hp : (itemCode (neighbor previous e)).length ≤ U := by
      rcases head_mem_or_default previous e.1.1 with hf | hf
      · change neighbor previous e = zeroItem at hf
        rw [hf,zeroItem_length]
        exact hu
      · exact hprev _ hf
    have hb := extend_length_le previous e
    change _ ≤ U+4*(listCode rowCode graph).length+40
    omega

private theorem iterate_graph (i : ℕ) (g : Graph) (xs : List Item) :
    ((update^[i]) (g,xs)).1 = g := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [Function.iterate_succ_apply', update] using ih

private theorem iterate_item_bound (g : Graph) (xs : List Item) (i : ℕ) :
    let L := (prodCode graphCode valuesCode (g,xs)).length
    ∀ y ∈ ((update^[i]) (g,xs)).2, (itemCode y).length ≤ (i+1)*(4*L+40) := by
  let L := (prodCode graphCode valuesCode (g,xs)).length
  have gLen : (graphCode g).length ≤ L := by simp [L,prodCode,pairBits_length]; omega
  have oldLen : (valuesCode xs).length ≤ L := by simp only [L,prodCode,pairBits_length]; omega
  change ∀ y ∈ ((update^[i]) (g,xs)).2, (itemCode y).length ≤ (i+1)*(4*L+40)
  induction i with
  | zero =>
    intro y hy
    have h := (code_le_of_mem itemCode (show y ∈ xs from hy)).trans oldLen
    omega
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    intro y hy
    let previous := ((update^[i]) (g,xs)).2
    have belong : y ∈ layer (g,previous) := by
      change y ∈ layer (((update^[i]) (g,xs)).1,previous) at hy
      rwa [iterate_graph] at hy
    have h22 : 22 ≤ (i+1)*(4*L+40) := by
      have h := Nat.mul_le_mul_right (4*L+40) (show 1 ≤ i+1 by omega)
      omega
    have hb := layer_item_bound g previous h22 ih y belong
    rw [Nat.succ_mul]
    omega

private theorem tableLength (g : Graph) (xs : List Item) (i : ℕ) :
    (((update^[i]) (g,xs)).2).length ≤ (prodCode graphCode valuesCode (g,xs)).length := by
  cases i with
  | zero =>
    have h := list_length_le_code itemCode xs
    simp only [Function.iterate_zero, id_eq, prodCode, pairBits_length, valuesCode]
    omega
  | succ i =>
    rw [Function.iterate_succ_apply']
    change (((update^[i]) (g,xs)).1.map _).length ≤ _
    rw [List.length_map, iterate_graph]
    have h := list_length_le_code rowCode g
    simp only [prodCode, pairBits_length, graphCode]
    omega

private noncomputable def growth : Polynomial ℕ := Polynomial.C 1000*(Polynomial.X+1)^3

private theorem iterate_growth (K : ℕ) (state : Graph×List Item) (i : ℕ) (hi : i≤K) :
    (prodCode graphCode valuesCode ((update^[i]) state)).length ≤
      growth.eval (K+(prodCode graphCode valuesCode state).length) := by
  obtain ⟨g,xs⟩ := state
  let L := (prodCode graphCode valuesCode (g,xs)).length
  let N := K+L
  let table := ((update^[i]) (g,xs)).2
  have hlen : table.length ≤ L := tableLength g xs i
  have narrow := iterate_item_bound g xs i
  have hbounded : (valuesCode table).length ≤ table.length*(2*((i+1)*(4*L+40))+2)+1 := by
    simpa [valuesCode,table] using
      listCode_length_map_bound itemCode id table ((i+1)*(4*L+40)) (fun x hx => narrow x hx)
  have hL : L ≤ N := by dsimp [N]; omega
  have hiN : i ≤ N := hi.trans (by dsimp [N]; omega)
  have hwidth := Nat.mul_le_mul (show i+1 ≤ N+1 by omega) (show 4*L+40 ≤ 4*N+40 by omega)
  have hcells := Nat.mul_le_mul (hlen.trans hL)
    (show 2*((i+1)*(4*L+40))+2 ≤ 2*((N+1)*(4*N+40))+2 by omega)
  have hg : (graphCode g).length ≤ L := by simp [L,prodCode,pairBits_length]; omega
  change (pairBits (graphCode (((update^[i]) (g,xs)).1)) (valuesCode table)).length ≤ growth.eval N
  rw [pairBits_length]
  rw [iterate_graph]
  calc
    _ ≤ 2*N + N*(2*((N+1)*(4*N+40))+2)+2 := by omega
    _ ≤ _ := by
      simp [growth]
      nlinarith [Nat.zero_le (N^2), Nat.zero_le (N^3)]

/-- Compute a specified horizon in a uniform bit program. The unary horizon is appropriate
for the dimension-bounded number of Bellman rounds. -/
def solve (z : ℕ × Graph) : List Item := ((update^[z.1]) (z.2,z.2.map start)).2

noncomputable def solveProgram : Procedure
    (prodCode (fun k : ℕ => List.replicate k true) graphCode) valuesCode solve := by
  let uc := fun k : ℕ => List.replicate k true
  let count := first uc graphCode
  let rows := second uc graphCode
  let state := rows.pair (initialProgram.comp rows)
  let execute := (updateProgram.iterate growth iterate_growth).comp (count.pair state)
  exact ((second graphCode valuesCode).comp execute).congrFun (fun _ => rfl)

theorem solve_deploy (o : OracleSpec.WordOracle) (x : ℕ × Graph) :
    let data := prodCode (fun k : ℕ => List.replicate k true) graphCode x
    (OracleSpec.BitCode.deploy solveProgram).ComputesWithin o data
      (3*solveProgram.bound.eval data.length+2*data.length+2)
      (fun history bits => history = [] ∧ bits = valuesCode (solve x)) :=
  OracleSpec.BitCode.deploy_correct solveProgram o x

end Table
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
