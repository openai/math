import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineCodec
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineGraph
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackReadout

/-! The serialized bit-scaling action performs the same primal and dual update as the
typed residual-network solver. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open OAI.Optimization.LinearProgramming.PriceGame.Market.Graph Quiver Potentials NumberBounds GridMachine GridMachine.Table

variable {m g : ℕ}

private theorem block_of_lookup (vals : List Item) (k off : ℕ) (f : Fin k → ℤ)
    (h : ∀ j : Fin k, (Readout.lookup vals (off+j.val)).1.1 = f j) :
    block (k,(off,vals)) = List.ofFn f := by
  rw [block, map_range_fin]
  exact congrArg List.ofFn (funext h)

/-- Read the selected path in the source row and copy each dual coordinate into its
proper output bank. The copied route uses the same ordered identifiers as `applyPath`. -/
theorem finish_serializes (n : Network (Fin m) (Fin g)) (D : ℕ) (π r : Vertex n → ℚ)
    (i : Fin m) (p : (v : Vertex n) → Plan n.weight r v) :
    finishStep (packSeed n D π i,(FlowMachine.packedFlow n.f,
        serializeValues (vertexIndex n) n.weight r (FlowMachine.arcID n) D p)) =
      (FlowMachine.packedFlow (applyPath n (p (start n i)).path),
        List.ofFn (fun e => Grid.coordinate D (p (.expert e)).total),
        List.ofFn (fun j : Fin (g+1) => Grid.coordinate D (p (.opt (finSuccEquiv g j))).total)) := by
  let vals := serializeValues (vertexIndex n) n.weight r (FlowMachine.arcID n) D p
  have hl (v : Vertex n) := Readout.lookup_serialized (vertexIndex n) n.weight r (FlowMachine.arcID n) D p v
  have pathEq : (Readout.lookup vals ((vertexIndex n) (start n i)).val).2 =
      FlowMachine.route n (p (start n i)).path :=
    congrArg (fun a : Item => a.2) (hl (start n i))
  have expEq : block (m,(0,vals)) = List.ofFn (fun e => Grid.coordinate D (p (.expert e)).total) := by
    apply block_of_lookup
    intro j
    simpa only [vals,serializePlan,Nat.zero_add,FlowMachine.Rows.index_expert,Fin.val_castAdd] using
      congrArg (fun a : Item => a.1.1) (hl (.expert j))
  have optEq : block (g+1,(m,vals)) =
      List.ofFn (fun j : Fin (g+1) => Grid.coordinate D (p (.opt (finSuccEquiv g j))).total) := by
    apply block_of_lookup
    intro j
    simpa only [vals,serializePlan,FlowMachine.Rows.index_option,Equiv.symm_apply_apply,Fin.val_natAdd] using
      congrArg (fun a : Item => a.1.1) (hl (.opt (finSuccEquiv g j)))
  rw [finishStep,sourceIndex_packSeed]
  simp only [packSeed,packBanks,List.length_ofFn]
  change (FlowMachine.update (FlowMachine.packedFlow n.f,
      (Readout.lookup vals ((vertexIndex n) (start n i)).val).2),
    block (m,(0,vals)),block (g+1,(m,vals))) = _
  rw [pathEq, FlowMachine.update_packedFlow, expEq, optEq]

theorem packEnv_pack (I : Input m g) (D : ℕ) (f : Fin m → Option (Fin g) → ℕ)
    (e : Fin m → ℚ) (o : Option (Fin g) → ℚ) :
    (packEnv I D (State.pack f e o)).2 =
      (FlowMachine.packedFlow f,List.ofFn (fun i => Grid.scaleInput D (e i)),
        List.ofFn (fun j : Fin (g+1) => Grid.scaleInput D (o (finSuccEquiv g j)))) := by
  simp only [packEnv,FlowMachine.Rows.encodeRaw,Input.network,State.flow_pack,State.pe_pack,State.po_pack,combine]

theorem marketUnit_simulates (I : Input m g) (D : ℕ) (s : State m g) (i : Fin m) (hD : 0 < D)
    (hc : ∀ e j, I.accepts e j → OnGrid D (I.intercept e j))
    (he : ∀ e, OnGrid D (s.pe e)) (ho : ∀ j, OnGrid D (s.po j)) :
    marketUnit (i.val,packEnv I D s) = (packEnv I D (I.unit s i)).2 := by
  let n := I.network s
  let dec := I.decideAcceptance s
  let π := combine n s.pe s.po
  let r := targetReward n.weight π (direct n i).toPath
  let ix := vertexIndex n
  let out := outgoing n dec
  let K := m+(g+1)-1
  let p (v : Vertex n) := Layer.lookup ix (plans ix n.weight r out K) v
  have pg (v : Vertex n) : OnGrid D (π v) := by
    cases v with
    | expert e => exact he e
    | opt o => exact ho o
  have rg (v : Vertex n) : OnGrid D (r v) := terminal_grid_of_direct n.weight π pg _ (direct_cost n i) v
  have eg {a b : Vertex n} (e : a ⟶ b) : OnGrid D (n.weight e) := n.weight_integral D hc e
  have grid (v : Vertex n) : OnGrid D (p v).total := plans_denominator ix n.weight r out D eg rg K v
  have body := Table.solve_serializes ix n.weight r out (FlowMachine.arcID n) D hD eg rg K
  rw [marketUnit,makeRowsInput_packEnv I s i D hD pg,FlowMachine.Rows.make_eq_serializeGraph,horizon_pack]
  change finishStep (packSeed n D π i,(FlowMachine.packedFlow n.f,Table.solve
    (K,Table.serializeGraph ix n.weight r out (FlowMachine.arcID n) D))) = _
  rw [body,finish_serializes]
  change (_,List.ofFn (fun e => Grid.coordinate D (p (.expert e)).total),
      List.ofFn (fun j : Fin (g+1) => Grid.coordinate D (p (.opt (finSuccEquiv g j))).total)) =
    (packEnv I D (State.pack (applyPath n (p (start n i)).path)
      (fun e => (p (.expert e)).total) (fun o => (p (.opt o)).total))).2
  rw [packEnv_pack]
  simp only [Grid.scaleInput_eq hD (grid _)]
  rfl

theorem marketDouble_simulates (I : Input m g) (D : ℕ) (s : State m g) :
    marketDouble (packEnv I D s) = (packEnv I D (Input.double s)).2 := by
  rw [Input.double,packEnv_pack]
  change ((FlowMachine.packedFlow s.flow).map (2*·),
      List.ofFn (fun i => Grid.scaleInput D (s.pe i)),
      List.ofFn (fun j : Fin (g+1) => Grid.scaleInput D (s.po (finSuccEquiv g j)))) = _
  simp [FlowMachine.packedFlow,FlowMachine.packedCells,List.map_ofFn,Function.comp_def]

/-- The binary action number is exactly the typed `none`/expert case of one bit plane. -/
theorem action_simulates (I : Input m g) (D : ℕ) (s : State m g) (a : Option (Fin m))
    (hD : 0 < D) (hc : ∀ e j, I.accepts e j → OnGrid D (I.intercept e j))
    (he : ∀ e, OnGrid D (s.pe e)) (ho : ∀ j, OnGrid D (s.po j)) :
    action (actionNumber a,packEnv I D s) =
      packEnv I D (a.elim (Input.double s) (I.unit s)) := by
  cases a with
  | none =>
    apply Prod.ext
    · rfl
    · exact marketDouble_simulates I D s
  | some i =>
    apply Prod.ext
    · rfl
    · simpa only [action,actionNumber,ScheduleMachine.actionNumber,Nat.succ_ne_zero,↓reduceIte,
        Nat.add_sub_cancel,Option.elim_some] using marketUnit_simulates I D s i hD hc he ho

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
