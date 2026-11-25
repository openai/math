import OAI.Computability.BorderVNP.FiniteEvaluatorCubeArenaDictionary
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleBoot
import OAI.Computability.BorderVNP.CubeTeamOwnedScannerWords

/-! # Actual initialization and group histories in the allocated field arena

The native initializer writes the static Boolean field deck using four primary
frame pointers. It has one return and preserves the scanner and the delivered
shared rows. Prepending that return extends the private assignment dictionary
to the complete installer and traversal, with the actual final cube operands.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeDeck

open BorderVNP.Cube BorderVNP.Cube.Tally RoutingISA VPVNP.BurstRAM
variable {w n b h K s : ℕ} {F : Type*} [Fintype F] (table : TableEntry n b h K s → F)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r : Bank w} {m : Memory w}

/-- Prepending the actual constant installer is a bijection on the returns of
every subsequent native program, keeping its final bank and memory. -/
noncomputable def prepend (c : Code) (x : Evaluator.Returns (install table) pub mac r m) :
    Evaluator.Returns c pub mac x.val.2.1 x.val.2.2 ≃ Evaluator.Returns (.seq (install table) c) pub mac r m := by
  let J := Evaluator.seqReturnEquiv (install table) c pub mac r m
  apply Equiv.ofBijective (fun y => J ⟨x,y⟩)
  constructor
  · intro y z h
    exact eq_of_heq (Sigma.mk.inj (J.injective h)).2
  · intro q
    obtain ⟨⟨v,y⟩,h⟩ := J.surjective q
    have det (p : Code) (hp : p.unsigned=true) : p.deterministic=true := by
      induction p <;> simp_all [Code.unsigned,Code.deterministic]
    obtain ⟨trace,regs,mem⟩ := v.property.unique_of_deterministic (det _ (CubeConstants.install_unsigned _).1) x.property
    obtain rfl : v=x := Subtype.ext (Prod.ext trace (Prod.ext regs mem))
    exact ⟨y,h⟩

/-- The initializer events precede the traversal, whose terminal memory and
register bank are the result of the actual combined program. -/
theorem prepend_val (c : Code) (x : Evaluator.Returns (install table) pub mac r m)
    (y : Evaluator.Returns c pub mac x.val.2.1 x.val.2.2) :
    (prepend table c x y).val=(x.val.1++y.val.1,y.val.2) := rfl

end FiniteEvaluator.CubeDeck

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open BorderVNP.Cube.TeamRows FiniteEvaluator RoutingISA VPVNP.BurstRAM DiagonalTallyPacketEmit
open scoped BigOperators Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (B : DiagonalTallyAllocation.Bounds) (task : Fin (R+1) → TypedTaskBuilder.Layout) (sw bw : ℕ)
variable (pub : Fin (R+1) → Arg → Word w) (mac : Fin (R+1) → TeamOpcode.Macros w 8)
variable (regs : Fin (R+1) → Bank w) (initial : Fin (R+1) → Memory w)

local notation "arena" => planArena L R header profile cells cables maxRows stride
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ V.owners R (Sigma.fst (Prod.fst raw))
local notation "decl" => Assignment.Routed.trueDeclaration L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis (V.owners R (Sigma.fst (Prod.fst raw)))
local notation "fresh" => CubeArena.Layout.stop arena
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "srcRows" => sharedWords decl (Assignment.Routed.physicalShared (V.owners R) (Prod.fst raw))

/-- Complete installer and traversal histories over the physical shared rows.
The fixed scalar deck is produced by the genuine first program from the frame
pointers. Every true return belongs to exactly one compatible private fiber
and supplies the allocated lookup in its own terminal memory. -/
theorem installed_arena_dictionary
    (room : ∀ t, (arena).ReplayRoom w (readings (pub t) 0))
    (scanner : ∀ t, (arena).ScannerWords (readings (pub t) 0) t.val (axis).val number (readings (pub t)) (readings (initial t)) (Prod.snd decl))
    (received : ∀ t, (arena).RawViews (readings (pub t) 0) t.val (axis).val number srcRows (initial t))
    (frameWords : ∀ t, let f := CubeAllocation.frame arena table B (task t) sw bw (V.teamPairs R raw t).length
      Frame.resident {f with count:=readings (initial t) ((pub t 0).val+46)} (readings (pub t)) (readings (initial t)))
    (tableWord : ∀ t, readings (initial t) ((pub t 0).val+47)=ptr)
    (dstWord : ∀ t, readings (initial t) ((pub t 0).val+71)=(CubeAllocation.after arena table B (task t) sw bw).ids)
    (wide : CubeDeck.minimumWidth F L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ w)
    (word : ∀ t, (CubeAllocation.after arena table B (task t) sw bw).packed ≤ 2^w)
    (fixed : ∀ p, L.table p=table) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((t : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups table)
        (pub t) (mac t) (regs t) (initial t)),
      ∀ f, let next := V.withPrivate R raw f
        let Y := V.allocatedInputs R next header profile cells cables maxRows stride table B task sw bw
        (∀ t, let out := E f t
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 t).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install table).slots + V.ownedTicks R raw header profile cells cables maxRows stride pub t ∧
            CubePacket.Prepared (Y t) (pub t) out.val.2.2 ∧
            CubePacket.Sources (Y t) (CubeAllocation.tasks arena table B (task t) sw bw)) ∧
          (∏ t, ∏ i, (Y t).scalar i) = cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2 := by
  let fr (t : Fin (R+1)) := CubeAllocation.frame arena table B (task t) sw bw (V.teamPairs R raw t).length
  let A := V.bankData R raw (arena).header.packetBase (arena).singleBank
  have space (t : Fin (R+1)) : (pub t 0).val+112 ≤ fresh ∧ CubeConstants.arenaEnd fresh (CubeDeck.entry table) < 2^w := by
    have length := congrArg List.length (V.numbered_pairs R raw t)
    have cap : (V.teamPairs R raw t).length ≤ (arena).vertexCap := length.symm ▸ CubeAllocation.team_count arena axis number t.val
    obtain ⟨lo,ds,_,_,rf,dst,top⟩ := CubeAllocation.rooms arena table B (task t) sw bw A rfl cap (room t).primary (word t)
    exact ⟨lo,ds.trans_lt (by omega)⟩
  have one (t : Fin (R+1)) : ∃ x : Evaluator.Returns (CubeDeck.install table) (pub t) (mac t) (regs t) (initial t),
      DiagonalResidueRAM.TraceOK x.val.1 [] x.val.1.length ∧ traceCost x.val.1 ≤ (CubeDeck.install table).slots ∧
        CubeDeck.At table (fr t) fresh (readings x.val.2.2) ∧ ∀ j < fresh, x.val.2.2 j=initial t j := by
    obtain ⟨_,_,recipes,_,_,zero,one,_,_⟩ := frameWords t
    obtain ⟨es,u,mu,run,cost,deck,keep,clean⟩ := CubeDeck.install_run table (fr t) fresh (pub t) (mac t) (regs t)
      (initial t) (space t).1 (space t).2 wide ⟨zero,one,recipes,tableWord t⟩
    exact ⟨⟨(es,u,mu),run⟩,⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (clean e he).1,fun e he => (clean e he).2⟩,cost,deck,keep⟩
  choose init ok cost boot kept using one
  let loaded (t : Fin (R+1)) := (init t).val.2.2
  have below (t : Fin (R+1)) (j : ℕ) (hj : j < 112) :
      readings (loaded t) ((pub t 0).val+j)=readings (initial t) ((pub t 0).val+j) :=
    congrArg Fin.val (kept t _ (by have := (space t).1; omega))
  have dir : (arena).pairDirectory ≤ fresh :=
    (arena).source_order.2.2.trans ((Nat.le_add_right _ _).trans (arena).separated.2.2.2.2.2)
  have newWords (t : Fin (R+1)) := (scanner t).transfer (room t).axes (room t).primary
    (out := readings (loaded t)) (fun j hj _ => congrArg Fin.val (kept t j (hj.trans_le dir)))
  have newViews (t : Fin (R+1)) : (arena).RawViews (readings (pub t) 0) t.val (axis).val number srcRows (loaded t) := by
    intro p side owned
    apply (received t p side owned).congr
    intro j hj
    have high := hj.2
    change j < (arena).pairBase+(arena).pairStride*(L.alphabet*L.alphabet) at high
    have eqn : (arena).pairBase+(arena).pairStride*(L.alphabet*L.alphabet) = (arena).cellBank := by
      rw [Nat.mul_comm (arena).pairStride,←pow_two]; rfl
    exact kept t j ((high.trans_le eqn.le).trans_le (arena).separated.2.2.2.2.2)
  have newFrame (t : Fin (R+1)) : Frame.resident {(fr t) with count:=readings (loaded t) ((pub t 0).val+46)}
      (readings (pub t)) (readings (loaded t)) := by
    have orig := frameWords t
    dsimp only [Frame.resident] at orig ⊢
    exact ⟨rfl,(below t 78 (by decide)).trans orig.2.1,(below t 79 (by decide)).trans orig.2.2.1,
      (below t 80 (by decide)).trans orig.2.2.2.1,(below t 45 (by decide)).trans orig.2.2.2.2.1,
      (below t 81 (by decide)).trans orig.2.2.2.2.2.1,(below t 82 (by decide)).trans orig.2.2.2.2.2.2.1,
      (below t 83 (by decide)).trans orig.2.2.2.2.2.2.2.1,(below t 84 (by decide)).trans orig.2.2.2.2.2.2.2.2⟩
  obtain ⟨E,cert⟩ := V.arena_dictionary R raw header profile cells cables maxRows stride table B task sw bw pub mac
    (fun t => (init t).val.2.1) loaded room newWords newViews boot newFrame
    (fun t => (below t 47 (by decide)).trans (tableWord t)) (fun t => (below t 71 (by decide)).trans (dstWord t)) word fixed
  let c := ownedGroups L.dimension L.bitWidth L.copies L.alternatives L.supply
  let J := Equiv.piCongrRight (fun t => CubeDeck.prepend table c (init t))
  refine ⟨E.trans J,fun f => ?_⟩
  obtain ⟨teams,prod⟩ := cert f
  refine ⟨fun t => ?_,prod⟩
  obtain ⟨bits,charge,prepared,sources⟩ := teams t
  change DiagonalResidueRAM.TraceOK ((init t).val.1++(E f t).val.1) _ ((init t).val.1++(E f t).val.1).length ∧ traceCost ((init t).val.1++(E f t).val.1) ≤ _ ∧ _
  exact ⟨by simpa only [List.nil_append,List.length_append] using (ok t).append bits,
    (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add (cost t) charge),prepared,sources⟩

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
