import OAI.Computability.VPVNP.PairRefreshTraversalAction
import OAI.Computability.VPVNP.PairRefreshResidentExact

/-!
# Exact execution of the chronological terminal refresh action

The accepted action fixes both the trace and the entire upper scratch update. A failed
diagonal or local map forces rejection for every continuation and every unused tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist bits g : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (degree n rowEnd child parent : ℕ)

local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "T" => plan B ties stride order
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "R" => TerminalLayout.privateRegions degree n rowEnd hist
local notation "A" => LeafArena.Regions.arguments R
local notation "hb" => LeafArena.Regions.histBase R
local notation "dir" => hb + hist + 12 + 2 * n
local notation "K" => MapCallWords.headCapacity (2 ^ S.portExponent) (2 ^ S.expanderExponent)
local notation "demand" =>
  blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) (Prod.fst v)
local notation "copies" => repetitions B.refresh demand
local notation "O" => sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g)

variable (room : Room B X choice v degree n rowEnd child parent hist bits)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (m : Memory bits) (oldHead newHead : ℕ) (G : W bits)

local notation "events" =>
  canonicalEvents B ties stride order X choice v degree n rowEnd child parent room old new
    m oldHead newHead G
local notation "upper" =>
  canonicalUpper B ties stride order X choice v degree n rowEnd child parent room old new

variable (U V : IncidenceDirectory bits) (start listHead : ℕ)

local notation "Pl" =>
  Allocation.plan X (S.degreeExponent 0) (2 ^ S.expanderExponent) t stride start
local notation "pub" => operands (Fin.val (O v)) parent newHead hb G
local notation "st" => word (bits := bits) oldHead
local notation "I" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand I)

variable {pcs regs : ℕ} (loc : Fin (body B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (bank : Fin (body B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11)

local notation "left" =>
  Segment.leftPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "right" =>
  Segment.rightPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "commonBank" => Function.Embedding.trans (locatorBank B ties stride order) bank
local notation "own" => Function.Embedding.trans (Function.Embedding.trans Function.Embedding.inr
  (Equiv.toEmbedding (RefreshResidentImage.Plan.registers T))) bank
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "wo" => ws (v, Prod.snd v)
local notation "wi" => ws (Equiv.symm perm (v, Prod.snd v))
local notation "supply" =>
  blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh choice
local notation "dia" => portDiagonal perm ws (Prod.fst v) (Prod.snd v) (oldHalf X v old)
  (segments X v S.graph.toSlotGraph S.port_order hd supply new)
local notation "named" => Option.map (List.map (RefreshResidentImage.Plan.ordinal T))
  (Prod.fst (runEntry B.refresh (fun _ => zero_lt_one) (EntryInput.demand I)
    (EntryInput.payload I) (Prod.snd v)
    (demandBits tieSource tieTarget (Prod.snd v) (EntryInput.demandBits I))
    (mapHalf S.portSupply (fun _ => inputBits) (EntryInput.supplyBits I))))

set_option maxHeartbeats 2500000 in
-- The exact trace specializes both native branches to the canonical dependent scratch update.
theorem canonical_body {fit :
    Fintype.card X.Base * 2 ^ S.portExponent * 2 ^ g * 2 ^ S.portExponent ≤ 2 ^ bits}
    (rows : ∀ j, M.code (loc j) =
      ((body B ties stride order).row loc dfs saved bank done j).resize bits)
    (apartD : ∀ i j, bank i ≠ dfs j) (apartS : ∀ i j, bank i ≠ saved j)
    (c : Config bits pcs regs) (entry : c.pc = left TraversalGeometry.reload.entry)
    {endAddr : ℕ} {offset : W bits} (endWord : c.reg (dfs 6) = (endAddr : W bits))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset (word hb))
    (oldWord : (c.reg (commonBank 11)).val = oldHead)
    (newWord : (c.reg (commonBank 4)).val = newHead)
    (siteWord : (c.reg (commonBank 7)).val = (O v).val)
    (parentWord : (c.reg (commonBank 0)).val = parent)
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits)
    (stored : Build.Stored X S.graph
      (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldCols : U.ActualColumns X m) (newCols : V.ActualColumns Y m)
    (oldData : NodeFields A child X (oldSite X v) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites v) new c.privateMem)
    (wide : 2 ^ S.portExponent < 2 ^ bits) (s : DFS.Scratch bits endAddr)
    (incoming : DFS.scratch endAddr c.privateMem = s) :
    let names := emitted B order X choice v old new
    match canonicalAction B ties stride order X choice v degree n rowEnd child parent room old new m
      oldHead newHead G s with
    | none => ∀ bs, ¬ DFS.Returns M c m bs
    | some (es, updated) =>
      ∃ out, ChildScan.Prefix M m c out [] es ∧
        es.length ≤ budget B ties stride order * (wo + wi + copies + 1) ∧
        countProbes es ≤ budget B ties stride order ∧ choiceBits es = [] ∧ out.pc = done ∧
        out.persistent = c.persistent ∧ (∀ j, (∀ i, j ≠ bank i) → out.reg j = c.reg j) ∧
        (∀ q : W bits, q.val < dir →
          (∀ l : Fin hist, q ≠ word (hb + l.val)) → out.privateMem q = c.privateMem q) ∧
        (∀ l : Fin hist, out.privateMem (word (hb + l.val)) = c.privateMem (word (hb + l.val)) +
          ((names.getD []).count l : W bits)) ∧ DFS.scratch endAddr out.privateMem = updated := by
  dsimp only
  unfold canonicalAction
  by_cases good : (emitted B order X choice v old new).isSome = true
  · rw [ite_eq_left good]
    have diagonal : dia = (1 : ℤ) := by
      by_contra bad
      simp only [emitted, ite_eq_right bad, Option.isSome_none, Bool.false_eq_true] at good
    have names : (named).isSome = true := by
      simp only [emitted, ite_eq_left diagonal] at good
      exact good
    obtain ⟨mid, pre, ep, priv, per, frame, pubEq, stEq⟩ :=
      enter_canonical B ties stride order loc dfs saved bank done M
      rows c entry endWord resident oldWord newWord siteWord parentWord
    obtain ⟨args, hdir, hhist⟩ :=
      canonical_data B ties stride order X choice v A U V m start parent child listHead
      oldHead newHead hb G (fit := fit) header row lanes
    have first : ChildScan.Prefix M m c mid [] (List.replicate 4 .tick) := fun fuel bs =>
      pre.execute fuel m bs
    have banks : RefreshResidentImage.Plan.Banks T dfs saved commonBank own := by
      refine ⟨fun _ j => apartD _ j, fun _ j => apartS _ j, ?_⟩
      intro a b eq
      have h : (Sum.inr a : Fin 14 ⊕ (T).Local) = Sum.inl b :=
        (T).registers.injective (bank.injective eq)
      contradiction
    have installed := (body_links B ties stride order loc dfs saved bank done M rows).2
    have oldEnd := TraversalGeometry.argument_end degree n rowEnd hist X (oldSite X v) old child
      room.childBound room.oldDegree room.oldWidth
    have newEnd := TraversalGeometry.argument_end degree n rowEnd hist Y (promotedSites v) new
      parent room.parentBound room.newDegree room.newWidth
    have space := TraversalGeometry.workspace_before_cache degree n rowEnd hist K copies room.large
      room.five room.copyBound
    have nfit : n < 2 ^ bits := by
      apply Nat.lt_of_le_of_lt _ room.capacity.room
      change n ≤ n + rowEnd * (2 * degree * n + 1) + hist + n ^ 5
      omega
    have wf (e) : ws e < 2 ^ bits := ((X.width_le_maxWireWidth _).trans room.oldWidth).trans_lt nfit
    obtain ⟨out, run, len, reads, tape, exit, per', keep, mem, hits, scratch⟩ :=
      (T).native_success_exact (right ∘ (T).locations) dfs saved commonBank own done M installed
        X choice v A child parent U V start m old new mid ep banks (pubEq.symm ▸ stEq.symm ▸ args)
        stored oldCols newCols (priv ▸ oldData) (priv ▸ newData) hb n dir hb
        (pubEq.symm ▸ stEq.symm ▸ hdir) (pubEq.symm ▸ stEq.symm ▸ hhist) oldEnd newEnd
        room.oldWidth room.newWidth (by omega) (by omega) space.2 room.capacity room.copyBound wide
        (wf _) (wf _) room.tableWidth endAddr s (priv ▸ incoming) diagonal names
    rw [pubEq, stEq] at run len reads tape
    obtain ⟨readBound, workBound⟩ := (T).uniform.choose_spec z v.2 wo wi copies
    refine ⟨out, first.trans run, ?_, ?_, ?_, exit, per'.trans per,
      fun j hj => (keep j (fun _ => hj _)).trans (frame j (hj _) (hj _)),
      fun q hq hn => (mem q hq hn).trans (congrFun priv q), ?_, scratch⟩
    · change (List.replicate 4 (.tick : Event bits) ++ _).length ≤
        ((T).uniform.choose + 4) * (wo + wi + copies + 1)
      rw [List.length_append, List.length_replicate, Nat.add_mul]
      have h := len.trans workBound
      have four : 4 ≤ 4 * (wo + wi + copies + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · change countProbes (List.replicate 4 (.tick : Event bits) ++ _) ≤ (T).uniform.choose + 4
      rw [countProbes_append, reads]
      change 0 + _ ≤ _
      omega
    · change choiceBits (List.replicate 4 (.tick : Event bits) ++ _) = []
      rw [PrimedInputRAM.Flow.choiceBits_append, tape]; rfl
    · intro l
      rw [hits, priv, emitted, ite_eq_left diagonal]
      rfl
  · rw [ite_eq_right good]
    obtain ⟨out, es, path, _, _, _, branch, _⟩ :=
      map_body B ties stride order loc dfs saved bank done M X choice v degree n rowEnd U V m
        start parent child listHead oldHead newHead old new rows apartD apartS c entry endWord
        resident oldWord newWord siteWord parentWord header row lanes stored oldCols newCols oldData
        newData room.childBound room.parentBound room.oldDegree room.newDegree room.oldWidth
        room.newWidth room.copyBound room.large room.five room.capacity wide room.tableWidth
    rw [ite_eq_right good] at branch
    have stop : M.program.step out = .reject := by
      change (M.code out.pc).run M.publicData out = _
      rw [branch]; rfl
    intro bs returned
    obtain ⟨fuel, rep, ran⟩ := (path.returns bs).mp returned
    cases fuel <;> simp only [execute, stop, reduceCtorEq] at ran

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
