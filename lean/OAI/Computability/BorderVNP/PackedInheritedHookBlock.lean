import OAI.Computability.BorderVNP.PackedInheritedHookLive
import OAI.Computability.BorderVNP.ShortenStaticRowsOccupancy

/-! # All and only the hook rows of the immutable terminal block

The reserved rectangles can contain holes and both ends of every live selected
cable. Reading the enable and destination columns leaves exactly the rows of
the requested terminal. Sorting these by the original sparse cable row gives
the saved verifier's hook order, including its empty-span equalities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile BankSite BankJoint BankPacket CellSparse DirectoryCircuit
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n old sites np C d h w : ℕ} (seed : S ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w)) (occupied : Fin (edgeCapacity e old n) → σ)
variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
variable (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (oldSite : p.layout.Site ↪ Fin sites) (oldEdge : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np)
variable (cell : (G e p bin perm positive first q).Site → Fin C) (aux : (G e p bin perm positive first q).Site → ℕ)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "sID" => siteRows e p oldSite seed
local notation3 "eID" => outputRows e p bin perm positive first q oldEdge seed
local notation3 "prog" => native e seed F counts cut occupied
variable {x : σ → Bool} (rep : Represents (G e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
    (outputRows e p bin perm positive first q oldEdge seed) portID F x)

private theorem source_of_side (src positive side : Bool)
    (h : (if src then positive else !positive) = side) : src = decide (positive = side) := by
  cases src <;> cases positive <;> cases side <;> simp_all

include rep in
omit [Fintype P] in
/-- The enable and destination columns are an exact membership test for the actual
hook rows of each terminal, even when both ends of an old self-loop are live. -/
theorem terminal_rows (mask : ∀ k, x (occupied k) = true ↔ k ∈ Set.range eID)
    (a : S) (t : Fin D × Bool) (r : Row old D) :
    ((prog).eval x (r,.inl ()) = true ∧ value (fun k => (prog).eval x (r,.inr (.inl k))) =
        (terminalIndex e seed F (a,t)).val) ↔
      ∃ z : {z : p.layout.Edge // bin z = some (perm t.1 a)},
        r = (oldEdge z.val,t.1,decide (positive z.val = t.2)) := by
  have ho := (exists_frame e seed F counts cut occupied).choose_spec.2 x r
  have hp : value (fun k => (prog).eval x (r,.inr (.inl k))) = value (x ∘ F.ptr (.inl (.inr (candidate e r)))) :=
    congrArg value (funext ho.2.1)
  rw [native_enabled,mask,hp]
  constructor
  · rintro ⟨hr,hd⟩
    have hm := (bandCandidate_mem_iff e p bin perm oldEdge seed (if r.2.2 then 0 else 1)
      r.1 (some (r.2.1,true))).mp hr
    obtain ⟨z,hz,hsel⟩ := hm
    have hk : (if r.2.2 then (0 : Fin 3) else 1).val < 2 := by cases r.2.2 <;> decide
    have charged := ((selected_iff (m := m) p bin perm z (some (r.2.1,true))).mp (hsel.mpr hk)).1
    obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp charged
    let a' := (perm r.2.1).symm s
    have hbin : bin z = some (perm r.2.1 a') := by rw [Equiv.apply_symm_apply]; exact hs
    let z' : {u : p.layout.Edge // bin u = some (perm r.2.1 a')} := ⟨z,hbin⟩
    have hh := (matched_hook e seed F counts p bin perm positive first q oldSite oldEdge portID cell aux rep a' r.2.1 z' r.2.2).1
    have hrow : (oldEdge z'.val,r.2.1,r.2.2) = r := Prod.ext hz rfl
    rw [hrow] at hh
    have he := (terminalIndex e seed F).injective (Fin.ext (hh.symm.trans hd))
    obtain ha : a' = a := congrArg Prod.fst he
    have ht : (r.2.1,if r.2.2 then positive z else !(positive z)) = t := congrArg Prod.snd he
    have hdir := congrArg (fun y : Fin D × Bool => y.1) ht
    have hside := congrArg (fun y : Fin D × Bool => y.2) ht
    have hsrc : r.2.2 = decide (positive z = t.2) := source_of_side _ _ _ hside
    exact ⟨⟨z,by rw [← ha,← hdir]; exact hbin⟩,Prod.ext hz.symm (Prod.ext hdir hsrc)⟩
  · rintro ⟨z,rfl⟩
    let src := decide (positive z.val = t.2)
    refine ⟨⟨seedHook e p bin perm a t.1 z src,(candidate_hook e seed p bin perm positive first q oldEdge a t.1 z src).symm⟩,?_⟩
    have hh := (matched_hook e seed F counts p bin perm positive first q oldSite oldEdge portID cell aux rep a t.1 z src).1
    have hs : (if src then positive z.val else !(positive z.val)) = t.2 := by
      cases hz : positive z.val <;> cases ht : t.2 <;> simp [src,hz,ht]
    rw [hs] at hh
    exact hh

omit [NeZero D] [Fintype P] [Field K] [Fintype S] in
/-- In the actually saved pack, the terminal's enumeration is strictly increasing
in the original public row number, including sparse old layouts. -/
theorem eligible_sparse_order (a : S) (i : Fin D) :
    (eligible (densePack p oldEdge) (CutCircuit.denseBin p.layout oldEdge bin) perm a i).Pairwise
      (fun u v => CutCircuit.denseRows p.layout oldEdge u.val < CutCircuit.denseRows p.layout oldEdge v.val) := by
  let p' := densePack p oldEdge
  let T := {z : p'.layout.Edge // CutCircuit.denseBin p.layout oldEdge bin z = some (perm i a)}
  have hs := eligible_increasing p' (CutCircuit.denseBin p.layout oldEdge bin) perm a i
  refine hs.imp ?_
  intro u v huv
  have h := (Names.denseName_lt p.layout oldEdge ((Names.denseSlot p.layout oldEdge).symm u.val)
    ((Names.denseSlot p.layout oldEdge).symm v.val)).mp
  apply h
  rw [(Names.denseSlot p.layout oldEdge).apply_symm_apply u.val,(Names.denseSlot p.layout oldEdge).apply_symm_apply v.val]
  exact huv

/-- Extract all nine serialized words from the native hook row. -/
noncomputable def payload (f : Frame σ (Row old D × Column d w)) (x : σ → Bool) (r : Row old D) : List ℕ :=
  List.ofFn fun j : Fin 9 => value (fun k => f.eval x (r,.inr (.inr (j,k))))

include rep in
/-- In the terminal's old-cable order the native rectangle supplies the complete list of
nine-word records expected by its persistent block, with neither a width nor a length cutoff. -/
theorem terminal_payloads (room : ∀ v,incoming G₀ v < 2^w)
    (names : S → ℕ) (a : S) (t : Fin D × Bool) (hone : 1 < 2^w)
    (hcount : value (fun k => counts.eval x (a,none,k)) = blocks p.layout bin perm m a)
    (hcut : ∀ z : {z : p.layout.Edge // bin z = some (perm t.1 a)}, ∀ col,
      value (fun k => cut.eval x ((oldEdge z.val,some (t.1,true)),col,k)) =
        CutCircuit.Result.read (descriptor p.layout bin perm m names z (some (t.1,true))) col)
    (fit : ∀ z : {z : p.layout.Edge // bin z = some (perm t.1 a)},
      Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*blocks p.layout bin perm m a +
        incoming G₀ ((G₀).dst (seedHook e p bin perm a t.1 z (decide (positive z.val = t.2)))) +
        count p.layout bin (perm t.1 a) < 2^w) :
    (eligible p bin perm a t.1).map (fun z => payload prog x (oldEdge z.val,t.1,decide (positive z.val = t.2))) =
      (InheritedProfile.hookRows e p bin perm positive first q a sID eID portID names t).map Packet.record := by
  unfold InheritedProfile.hookRows
  rw [List.map_map]
  apply List.map_congr_left
  intro z _
  let src := decide (positive z.val = t.2)
  let data := Packet.record (terminalHook e p bin perm positive first q a id (workAt e p bin perm positive first q)
    sID eID portID names t.1 z src)
  have hn : data.length = 9 := rfl
  have h := (native_live e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID
    cell aux rep room names a t.1 z src hcount (hcut z) hone (fit z)).2
  change payload prog x (oldEdge z.val,t.1,src) = data
  apply List.ext_getElem
  · rw [payload,List.length_ofFn,hn]
  · intro j hj hk
    have hj' : j < 9 := hk.trans_eq hn
    refine (List.getElem_ofFn (f := fun l : Fin 9 => value (fun k => (prog).eval x
      ((oldEdge z.val,t.1,src),.inr (.inr (l,k))))) hj).trans ?_
    exact (h ⟨j,hj'⟩).trans (by change data[j]?.getD 0 = _; rw [List.getElem?_eq_getElem hk]; rfl)

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
