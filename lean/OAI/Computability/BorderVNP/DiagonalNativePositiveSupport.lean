import OAI.Computability.BorderVNP.DiagonalPhysicalPinStart
import OAI.Computability.BorderVNP.DiagonalNativeProfileReject
import OAI.Computability.BorderVNP.DiagonalNativePreparedRoute

/-! # Joint reachability of the complete pre-call stage on the signed exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube

variable {dim box lanes selectors symbols n w R : ℕ} {gen : Fragment IO}
    (id : TableEntry dim box lanes selectors symbols → ℕ)
local notation "groups" => scheduleGroups dim (Tally.selectorWidth dim selectors lanes)
local notation "args" => signedInputs id (TeamRows.ownedGroups dim box lanes selectors symbols)

/-- Every genuinely accepting evaluation has a complete returning pin and public
preparation. This extraction is independent of the evaluator clock or reader value. -/
noncomputable def prefixOfBody (U : PinStart gen n w)
    (body : Returns (signedBody id) U.pub (install gen n U.routines) U.bank U.memory) : U.Prefix id := by
  let mac := install gen n U.routines
  let parts := (evaluateReturnEquiv U.pub mac epochPlacement groups args signedOccurrences U.bank U.memory U.pins).symm body
  let pin := U.pins parts.1
  let rest := (expansionReturnEquiv U.pub mac pin.val.2.1 pin.val.2.2 epochPlacement groups args signedOccurrences).symm parts.2.1
  exact ⟨parts.1,rest.1⟩

/-- On the joint support any complete local preparation can be used in a full
tuple of genuine preparations at the same exterior. Its report need not agree
with the later private checker or the broadcast subtotal. -/
theorem jointSupport_extend (U : Fin (R+1) → PinStart gen n w) (supported : jointSupport id U)
    (u : Fin (R+1)) (localPrefix : (U u).Prefix id) :
    ∃ all : (v : Fin (R+1)) → (U v).Prefix id, all u=localPrefix := by
  classical
  exact ⟨Function.update (fun v => (supported v).some) u localPrefix,Function.update_self ..⟩

/-- The upper-bound hypothesis for the actual argument return can be established
by considering it in a full tuple on the same supported exterior. -/
theorem jointSupport_extend_arguments (U : Fin (R+1) → PinStart gen n w) (supported : jointSupport id U)
    (u : Fin (R+1)) (b : Fin (U u).guessWidth → Bool) :
    let T := U u
    let mac := install gen n T.routines
    ∀ pre : Returns (beforeRoute epochPlacement groups) T.pub mac (T.pins b).val.2.1 (T.pins b).val.2.2,
    ∀ routeRun : Returns route T.pub mac pre.val.2.1 pre.val.2.2,
    ∀ input : Returns args T.pub mac routeRun.val.2.1 routeRun.val.2.2,
      ∃ all : (v : Fin (R+1)) → (U v).Prefix id,
        (all u).2.val.1 = pre.val.1++(routeRun.val.1++input.val.1) ∧
        (all u).2.val.2=input.val.2 := by
  intro T mac pre routeRun input
  let tail := routeRun.property.seq input.property
  have full := (Runs.block_append_iff (a := [epochPlacement,Packing.Directory.ISA.program,groups]) (b := [route,args])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)).mpr (pre.property.seq tail)
  let joinedPrefix : T.Prefix id := ⟨b,⟨(pre.val.1++(routeRun.val.1++input.val.1),input.val.2),full⟩⟩
  obtain ⟨all,eqn⟩ := jointSupport_extend id U supported u joinedPrefix
  exact ⟨all,eqn ▸ rfl,eqn ▸ rfl⟩

end RoutingISA.Evaluator.PinStart

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator
open BorderVNP.Cube PackedHistoryCircuit

variable {dim box lanes selectors symbols R r t d link inner n w : ℕ} {Edge : Type}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (gen : Fragment IO)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w)
    (reg : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
local notation "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)

/-- A team with no complete pre-call prefix contributes zero to the positive signed
product for every cutoff. The proof extracts the prefix from any accepted machine path.
It does not require a cost bound on malformed received packet bytes. -/
theorem positiveMasked_zero_of_prefix_empty (u : Fin (R+1)) (ticks burst clock : ℕ)
    (U : PinStart gen n w) (trace : List (TeamRAM.Event w)) (z : Bank w) (saved : Memory w) :
    let ad := args u
    let F := G.processorFields u pin ext ad.ibase ad.hbase ad.starbase
    let f := G.transferFrame u ad.header ad.dst
    Runs (pub u) mac JointHeader.bootHeader (reg u) (processorMemory F w) trace z saved →
    f.Stable (readings z) → (saved f.dst).val ≠ 0 →
    U.pub=pub u → U.routines=mac → U.bank=Function.update z 10 (saved f.dst) → U.memory=saved →
    ¬ Nonempty (U.Prefix id) → positiveMaskedNativeValue G (signedBody id) mac pub reg args pin ticks burst clock ext u=0 := by
  intro ad F f boot stable positive publicEq routines start memory empty
  by_cases tag : modeTag (w := w) G args pin ext u=0
  · exact ite_eq_left tag
  rw [positiveMaskedNativeValue,ite_eq_right tag]
  let M := processorMachine (signedProgram id) (pub u) mac (reg u) F
  have impossible : IsEmpty (NativePath M ticks burst clock) := by
    constructor
    intro path
    obtain ⟨⟨v,mv,run⟩,_⟩ := (signedProgram_execute_iff id).mp path.property.1
    obtain ⟨z',mz,first,head,_,initial,copy⟩ := Runs.seq_iff.mp boot
    obtain ⟨bs,_,body⟩ := (evaluation_startup_iff f (signedBody id) initial copy stable positive).mp run
    apply empty
    apply Nonempty.intro ∘ U.prefixOfBody id
    refine ⟨(bs,v,mv),?_⟩
    rw [publicEq,routines,start,memory,←siteLibrary_installed gen n]
    exact body
  change nativeValue M ticks burst clock=0
  simp [nativeValue]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
