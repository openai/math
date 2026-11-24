import OAI.Computability.VPVNP.PairSimulationLeafFront
import OAI.Computability.VPVNP.PairSimulationLeafBootHandoff
import OAI.Computability.VPVNP.PairSimulationRouteBank

/-!
# Native instruction image of a descriptor leaf

The address reader shares the DFS node slot. A transit cursor returns directly
from the route check. At cursor zero, seven instructions copy the site and header
and supply the two private-memory pointers to the stack initializer. The
initialized stack pointers are the ones used by the auxiliary processor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafImage

open BurstRAM PrivateRAM RAMTape LeafStartup

set_option synthInstance.maxSize 10000

/-- Internal labels of the leaf call. The return label belongs to its caller. -/
inductive Label where
  | address (i : Fin 20)
  | prepare (i : RoutePrepare.Stage)
  | route (i : RouteBank.Address)
  | handoff (i : Fin 7)
  | boot (i : LeafBoot.Label)
  | stack (q : Option auxiliaryProcessor.State) (i : Fin 7)

noncomputable instance : Fintype Label := by classical exact derive_fintype% _

/-- The address reader uses the caller's node register and eight private slots. -/
inductive Reg where
  | dfs (i : Fin 9)
  | address (i : {j : LeafAddress.Reg // j ≠ .node})
  | route (i : Fin 32)
  | boot (i : LeafBoot.Reg)

noncomputable instance : Fintype Reg := by classical exact derive_fintype% _

/-- Public operands of the leaf image, grouped into address fields, private arena fields, and
input size. -/
inductive Pub where
  | address (j : LeafAddress.Field)
  | arena (j : RoutePrepare.Field)
  | size
  deriving DecidableEq, Fintype

variable {p r k w : ℕ}

private def leafName (j : LeafAddress.Reg) : Reg :=
  if h : j = .node then .dfs 7 else .address ⟨j,h⟩

private theorem leafName_injective : Function.Injective leafName := by
  let back : Reg → LeafAddress.Reg := fun
    | .address j => j.val
    | _ => .node
  apply Function.LeftInverse.injective (g := back)
  intro i
  by_cases h : i = .node <;> simp [back,leafName,h]

variable (pc : Label → Fin p) (reg : Reg ↪ Fin r) (pub : Pub → Fin k) (ret : Fin p)

/-- Embed the nine caller DFS registers into the register bank of the linked leaf. -/
def dfsReg : Fin 9 ↪ Fin r := ⟨fun i => reg (.dfs i),fun _ _ h => Reg.dfs.inj (reg.injective h)⟩

/-- Assign the address decoder's registers, sharing its node input with DFS register 7. -/
def leafReg : LeafAddress.Reg ↪ Fin r := ⟨fun i => reg (leafName i),reg.injective.comp leafName_injective⟩

/-- Assign the routing test's 32 registers to their slots in the linked leaf. -/
def routeReg : Fin 32 ↪ Fin r := ⟨fun i => reg (.route i),fun _ _ h => Reg.route.inj (reg.injective h)⟩

/-- Assign the leaf initializer's registers to their slots in the linked leaf. -/
def bootReg : LeafBoot.Reg ↪ Fin r := ⟨fun i => reg (.boot i),fun _ _ h => Reg.boot.inj (reg.injective h)⟩

@[simp] theorem node_dfs : leafReg reg .node = dfsReg reg 7 := rfl

theorem dfs_preserved (i : Fin 9) : LeafAddress.Preserved (leafReg reg) (dfsReg reg i) := by
  intro j hj
  apply reg.injective.ne
  simp [leafName,hj]

theorem dfs_ne_route (i : Fin 9) (j : Fin 32) : dfsReg reg i ≠ routeReg reg j :=
  reg.injective.ne (by intro h; cases h)

theorem dfs_ne_boot (i : Fin 9) (j : LeafBoot.Reg) : dfsReg reg i ≠ bootReg reg j :=
  reg.injective.ne (by intro h; cases h)

theorem dfs_offBoot (i : Fin 9) : dfsReg reg i ∉ Set.range (bootReg reg) :=
  fun ⟨j,h⟩ => dfs_ne_boot reg i j h.symm

theorem dfs_ne_stack (i : Fin 9) (j : StackMachine.Register ScalarPort) :
    dfsReg reg i ≠ LeafBoot.stack (bootReg reg) j := dfs_ne_boot reg i _

theorem leaf_ne_route (i : LeafAddress.Reg) (j : Fin 32) : leafReg reg i ≠ routeReg reg j := by
  apply reg.injective.ne
  by_cases h : i = .node <;> simp [leafName,h]

theorem leaf_ne_boot (i : LeafAddress.Reg) (j : LeafBoot.Reg) : leafReg reg i ≠ bootReg reg j := by
  apply reg.injective.ne
  by_cases h : i = .node <;> simp [leafName,h]

theorem dfs_not_written (i : Fin 9) : ¬ LeafBootHandoff.Written (bootReg reg) (dfsReg reg i) := by
  intro h
  rcases h with h | h | h | h | h <;> exact dfs_ne_boot reg i _ h

/-- Locate an initializer instruction using its boot label in the linked leaf image. -/
def bootPC : LeafBoot.Label → Fin p := pc ∘ Label.boot
/-- Locate the specified native instruction row of an auxiliary stack-machine state. -/
def stackPC (q : Option auxiliaryProcessor.State) (i : Fin 7) : Fin p := pc (.stack q i)

/-- Connect the address decoder and routing instructions to the cursor-zero handoff and the
caller's transit return. -/
def front : LeafFront.Program p r k where
  addressPC := pc ∘ Label.address
  leaf := leafReg reg
  addressPub := pub ∘ Pub.address
  preparePC := pc ∘ Label.prepare
  preparePub := pub ∘ Pub.arena
  route := RouteBank.program (pc ∘ Label.route) (routeReg reg)
  init := pc (.handoff 0)
  transit := ret
  apart := leaf_ne_route reg

/-- Literal-width five retains the constants of the geometry and initializer
rows. The placement functions and the return label are supplied by the host. -/
noncomputable def instruction : Label → Instr 5 p r k
  | .address i => LeafAddress.instruction (pc ∘ Label.address) (leafReg reg) (pub ∘ Pub.address)
      (pc (.prepare (.inl 0))) (pc (.prepare (.inl 0))) i
  | .prepare i => RoutePrepare.instruction (pc ∘ Label.prepare) (routeReg reg) (leafReg reg)
      (pub ∘ Pub.arena) ((front pc reg pub ret).route.pc 0) i
  | .route (.inl a) => (RouteBank.text (pc ∘ Label.route) (routeReg reg) (.inl a)).resize 5
  | .route (.inr i) =>
      if i = 0 then .jumpEq (routeReg reg 0) (routeReg reg 17) (pc (.handoff 0)) ret else .reject
  | .handoff i => LeafBootHandoff.instruction (pc ∘ Label.handoff) (bootReg reg) (leafReg reg)
      (pub ∘ Pub.arena) (bootPC pc (.pre 0)) i
  | .boot i => LeafBoot.instruction (bootPC pc) (bootReg reg) (pub .size) (stackPC pc auxiliaryEntry 0) i
  | .stack q i => StackMachine.instruction auxiliaryCode (stackPC pc) (LeafBoot.stack (bootReg reg)) ret q i

/-- All native interfaces used by the caller's execution proof. -/
structure Linked (M : Machine w p r k) : Prop where
  front : (LeafImage.front pc reg pub ret).Linked M
  handoff : ∀ i, M.code (pc (.handoff i)) = LeafBootHandoff.instruction (pc ∘ Label.handoff)
    (bootReg reg) (leafReg reg) (pub ∘ Pub.arena) (bootPC pc (.pre 0)) i
  boot : LeafBoot.Linked (bootPC pc) (bootReg reg) (pub .size) (stackPC pc auxiliaryEntry 0) M
  stack : StackMachine.Linked M auxiliaryCode (stackPC pc) (LeafBoot.stack (bootReg reg)) ret

private theorem resize_one (i : Instr 1 p r k) : (i.resize 5).resize w = i.resize w := by
  cases i <;> try rfl
  case constant dst v next => simp only [Instr.resize,resize_literal (by decide : 1 ≤ 5)]

theorem linked (M : Machine w p r k)
    (rows : ∀ i, M.code (pc i) = (instruction pc reg pub ret i).resize w) :
    Linked pc reg pub ret M := by
  constructor
  · constructor
    · intro i
      change M.code (pc (.address i)) = _
      rw [rows (.address i)]
      simp only [instruction]
      rw [← LeafAddress.resize_instruction (w := 5), resize_one, LeafAddress.resize_instruction]
      rfl
    · intro i
      exact (rows (.prepare i)).trans (RoutePrepare.resize_instruction ..)
    · apply RouteBank.linked
      intro a
      exact (rows (.route (.inl a))).trans (resize_one _)
    · exact rows (.route (.inr 0))
    · exact rows (.route (.inr 1))
  · intro i
    rw [rows (.handoff i)]
    simp only [instruction]
    rw [← LeafBootHandoff.resize_instruction (w := 5),resize_one,LeafBootHandoff.resize_instruction]
  · intro i
    exact (rows (.boot i)).trans (LeafBoot.resize_instruction ..)
  · intro q i
    change M.code (pc (.stack q i)) = _
    rw [rows (.stack q i)]
    simp only [instruction]
    rw [← StackMachine.resize_instruction (w := 5),resize_one,StackMachine.resize_instruction]

/-- Canonical finite image with an accepting return. An enclosing DFS template
can instead use `instruction` at its own labels and supply its loop continuation. -/
abbrev Address := Label ⊕ Unit
/-- Number the internal leaf instructions in the standalone template's address space, which
also reserves a return address. -/
noncomputable def locations : Label → Fin (Fintype.card Address) := fun i => Fintype.equivFin Address (.inl i)
/-- The standalone template's designated return address, occupied by an accepting instruction. -/
noncomputable def returnPC : Fin (Fintype.card Address) := Fintype.equivFin Address (.inr ())
/-- Number the named leaf registers for use by the standalone template. -/
noncomputable def registers : Reg ↪ Fin (Fintype.card Reg) := (Fintype.equivFin Reg).toEmbedding
/-- Number the named leaf operands for use in the standalone template's public data. -/
noncomputable def publics : Pub ≃ Fin (Fintype.card Pub) := Fintype.equivFin Pub

/-- The standalone native leaf program with five-bit literals, entry at the first
address-decoding row, and an accepting return instruction. -/
noncomputable def template : Template (Fintype.card Address) (Fintype.card Reg) (Fintype.card Pub) where
  literalWidth := 5
  entry := locations (.address 0)
  code i := match (Fintype.equivFin Address).symm i with
    | .inl a => instruction locations registers publics returnPC a
    | .inr _ => .accept

theorem template_linked (data : Fin (Fintype.card Pub) → Word w) :
    Linked locations registers publics returnPC (template.instantiate w data) := by
  apply linked
  intro i
  simp [Template.instantiate,template,locations]

theorem template_return (data : Fin (Fintype.card Pub) → Word w) :
    (template.instantiate w data).code returnPC = .accept := by
  simp [Template.instantiate,template,returnPC,Instr.resize]

end PairSimulation.LeafImage

end VPVNP
end Computability
end OAI
