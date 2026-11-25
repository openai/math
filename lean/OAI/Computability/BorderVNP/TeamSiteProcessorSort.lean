import OAI.Computability.BorderVNP.TeamSiteProcessor
import OAI.Computability.BorderVNP.TeamContractionReplay

/-! # Signed terminal validation of the actual emitted record buffer

Closing a processor's physical buffer and running the sorter preserves the incoming
path sign precisely when all of that owner's comparison and boundary checks succeed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape RAMSerialization Layout TeamTapeSorting
open scoped Classical

variable {Q Γ : Type} {p r k a m g d e w n : ℕ}

/-- Stream positions needed by the physical sorter, apart from the shared record buffer. -/
structure RouteReady (n : ℕ) (f : Fields d e w) (v : Word d) (other : Option (Word d))
    (s : Stacks (Layout.Port r k (m*g))) : Prop where
  literal : ∃ tail, s metadata = TeamTapeInputRoute.metadataBits n e w v other ++ tail
  wires : ∃ rest, s incident = TeamTapeInputRoute.ownerBits f v other ++ rest
  width : (s (.route (.inr TeamTapeInputRoute.widthSource))).length = w
  bucket : (s (.route (.inr TeamTapeInputRoute.bucket))).length = 2^e
  suffix : s (.route (.inr .suffixSize)) = []
  bits : s (entry (.inl .bits)) = []
  high : s (entry (.inl .high)) = []
  tmp : s (entry (.inl .scratch)) = []
  count : s (.route (.inr (.work .count))) = []
  scratch : s (.route (.inr (.work .tmp))) = []
  post : ∀ b i, s (.route (.inr (.post b i))) = []
  guard : ∀ i, s (.route (.inl i)) = []

/-- The router's fixed input fields are separate from all word-record destinations. -/
theorem RouteReady.installBuffer {f : Fields d e w} {v other}
    {s : Stacks (Layout.Port r k (m*g))} (ready : RouteReady n f v other s) (b : Stacks RecordBuffer.Port) :
    RouteReady n f v other (installStacks buffer s b) := by
  have eq {j : Layout.Port r k (m*g)} (h : ∀ i, buffer i ≠ j) :=
    installStacks_outside s b h
  rcases ready.literal with ⟨t,ht⟩; rcases ready.wires with ⟨z,hz⟩
  constructor
  · exact ⟨t,(eq (by simp)).trans ht⟩
  · exact ⟨z,(eq (by simp)).trans hz⟩
  · rw [eq (by simp)]; exact ready.width
  · rw [eq (by simp)]; exact ready.bucket
  · exact (eq (by simp)).trans ready.suffix
  · exact (eq (by simp)).trans ready.bits
  · exact (eq (by simp)).trans ready.high
  · exact (eq (by simp)).trans ready.tmp
  · exact (eq (by simp)).trans ready.count
  · exact (eq (by simp)).trans ready.scratch
  · exact fun j i => (eq (by simp)).trans (ready.post j i)
  · exact fun i => (eq (by simp)).trans (ready.guard i)

private theorem constant_paths {K S : Type} [DecidableEq K] (C : StackCode K S) (sg : Option Bool)
    (t : ℕ) (q : S) (s : Stacks K) :
    TeamStack.paths (withWeight sg C) (fun _ => sg.getD false) t q s = (TeamPrivateCall.sign sg).value * (stackPaths C t q s : ℤ) := by
  induction t generalizing q s with
  | zero => simp [TeamStack.paths,stackPaths]
  | succ t ih =>
    rw [TeamStack.paths,stackPaths]
    rw [show withWeight sg C q = (match C q with | .halt b => .halt (b && sg.isSome) | op => op) from rfl]
    cases C q with
    | halt b => rcases sg with _ | (_ | _) <;> cases b <;> rfl
    | choose l r => simp [ih,mul_add]
    | _ => exact ih ..

/-- With a closed canonical block, the actual two-lane terminal count is the sign times
the owner validity indicator. This checks arbitrary physical wire assignments. -/
theorem sort_value (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w) (f : Fields d e w) (v : Word d)
    (other : Option (Word d)) (rows : Word d → List (WordRecord w))
    (empty : ∀ u, other = some u → rows u = []) (s : Stacks (Layout.Port r k (m*g)))
    (ready : RouteReady n f v other s) (hd : d ≤ n) (hw : w ≤ n) (hc : 2^e ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize d e w ≤ n)
    (closed : s (buffer .output) = List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) (rows v))))
    (fuel : ℕ) (budget : 600*(n+1)^2+2*siteBudget d e w+1 ≤ fuel) :
    TeamStack.paths (code P lib) negative fuel (.sort sg (some TeamTapeInputRoute.Verify.processor.body.entry)) s =
      if TeamTapeInputRoute.Verify.ownerValid hw₂ cap f (rowInput e rows) v other then (TeamPrivateCall.sign sg).value else 0 := by
  let raw := s ∘ Layout.Port.route ∘ Sum.inr
  have eq : s ∘ Layout.Port.route = TeamTapeInputRoute.Verify.initial raw := by
    funext i; cases i with | inl i => exact ready.guard i | inr i => rfl
  rcases ready.literal with ⟨tail, hi⟩; rcases ready.wires with ⟨rest, hs⟩
  have sorter := (TeamTapeInputRoute.Verify.processor_spec n hw₂ cap f v other rows empty raw tail rest hd hw hc hL
    hi hs ready.width ready.bucket ready.suffix ready.bits ready.high ready.tmp ready.count
    ready.scratch ready.post closed fuel budget).1 (fun _ _ => 0)
  have lift := TeamGuard.paths_lift (src := withWeight sg TeamTapeInputRoute.Verify.processor.body.standalone) (target := code P lib)
    (neg := fun _ => sg.getD false) (neg' := negative) Layout.Port.route (fun _ _ h => Layout.Port.route.inj h)
    (.sort sg) s (fun _ => rfl) (fun _ => rfl) fuel (some TeamTapeInputRoute.Verify.processor.body.entry) (TeamTapeInputRoute.Verify.initial raw)
  rw [installStacks_eq (fun _ _ h => Layout.Port.route.inj h) s (TeamTapeInputRoute.Verify.initial raw) (congrFun eq)] at lift
  rw [lift,constant_paths,Routine.stackPaths_close]
  simp only [Bool.toNat_false,ite_self]
  refine (congrArg (fun z : ℕ => (TeamPrivateCall.sign sg).value*(z : ℤ)) sorter).trans ?_
  split <;> simp_all

/-- All of the shared records, with canonical padding, are sent to that same physical
terminal checker. The time spent closing is explicit. -/
theorem closeSort_value (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (sg : Option Bool)
    (n : ℕ) (hw₂ : 2 ≤ w) (cap : 2^d*2^e < 2^w) (f : Fields d e w) (v : Word d)
    (other : Option (Word d)) (rows : Word d → List (WordRecord w))
    (empty : ∀ u, other = some u → rows u = []) (s : Stacks (Layout.Port r k (m*g)))
    (ready : RouteReady n f v other s) (hd : d ≤ n) (hw : w ≤ n) (hc : 2^e ≤ n)
    (hL : TeamTapeInputRoute.comparisonSize d e w ≤ n)
    (records : RecordBuffer.Holds hw₂ (2^e) (rows v) (s ∘ buffer))
    (fuel : ℕ) (budget : 600*(n+1)^2+2*siteBudget d e w+1 ≤ fuel) :
    let t := (4*2^e-(rows v).length)*(25*w+12)+1+(2*(4*2^e*5*w)+1)
    TeamStack.paths (code P lib) negative (fuel+t) (.close sg RecordBuffer.close.body.entry) s =
      if TeamTapeInputRoute.Verify.ownerValid hw₂ cap f (rowInput e rows) v other then (TeamPrivateCall.sign sg).value else 0 := by
  intro t
  let out := Function.update (Function.update (Function.update (s ∘ buffer) .remaining []) .reverseBuffer [])
    .output (Boundary.blockBytes (List.ofFn (SortReplay.emittedBlock hw₂ e (rows v))))
  have hclose := SortReplay.close_emittedBlock records
  have inj : Function.Injective (buffer (r := r) (k := k) (d := m*g)) := by intro i j he; simpa using he
  have hr := TeamLink.routine hclose (code P lib) buffer inj (.close sg)
    (.sort sg (some TeamTapeInputRoute.Verify.processor.body.entry)) s (fun _ => rfl)
  rw [installStacks_eq inj s (s ∘ buffer) (fun _ => rfl)] at hr
  rw [TeamGuard.runs_paths hr negative fuel]
  apply sort_value P lib sg n hw₂ cap f v other rows empty (installStacks buffer s out)
    (ready.installBuffer _) hd hw hc hL _ fuel budget
  rw [installStacks_at inj]
  rw [show out .output = Boundary.blockBytes (List.ofFn (SortReplay.emittedBlock hw₂ e (rows v))) from Function.update_self ..]
  exact SortReplay.emittedBlock_bytes ..

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
