import OAI.Computability.BorderVNP.PackedFrozenHookOrder
import OAI.Computability.BorderVNP.PackedInheritedHookSavedBlock
import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Frozen-tape schema of the immutable terminal hooks

The fixed rectangle carries the true enable, stable owner, and all nine scalar
fields of the native equality row. Its two bit addresses are tagged for later
cell-local relocation. Grouping by a terminal recovers its saved hook rows in
public old-cable order, with no records for old sites, origins, or paid boxes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.HookTape

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open InheritedProfile InheritedHook BankSite BankJoint BankPacket CellSparse
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical FrozenTape
open scoped Classical

variable {D old w d : ℕ}

/-- The two base addresses, at ordinals three and six, move with their owning site. -/
def tags : List Kind := [.plain,.plain,.plain,.bitAddress,.plain,.plain,.bitAddress,.plain,.plain]

/-- Frozen payload pin indexed by the reserved row, one of nine scalar fields, and its bit. -/
abbrev Data (old D w : ℕ) := Row old D × Fin 9 × Fin w

/-- The static hook rectangle as a persistent nine-scalar tape. -/
noncomputable def schema (old D w : ℕ) : FrozenTape.Schema (Row old D) (Data old D w) :=
  ⟨rows old D,fun _ => tags,fun _ => w,fun r i j => (r,i,j)⟩

variable {σ : Type*} [Fintype σ] (f : Frame σ (Row old D × Column d w))

/-- Reordering the already emitted pins into the owner's frozen-tape interface costs no gates. -/
noncomputable def asTape : Frame σ (FrozenTape.Pins (Row old D) (Data old D w) d) :=
  f.select fun
    | .inl (r,.inl u) => (r,.inl u)
    | .inl (r,.inr j) => (r,.inr (.inl j))
    | .inr (r,i,j) => (r,.inr (.inr (i,j)))

theorem asTape_size : (asTape f).size = f.size := rfl

/-- The freeze operation retains the actual native enable and every bit of its owner key. -/
theorem asTape_owner (x : σ → Bool) (r : Row old D) :
    (asTape f).eval x (.inl (r,.inl ())) = f.eval x (r,.inl ()) ∧
      owner ((asTape f).eval x) r = value (fun j => f.eval x (r,.inr (.inl j))) := by
  simp only [asTape,FrozenTape.owner,Frame.select_eval,and_self]

/-- The physical nine words of a live native equality decode into exactly the marked record. -/
theorem read_equal (x : σ → Bool) (r : Row old D) (n span : ℕ) (p q : Port)
    (hr : ∀ j : Fin 9,value (fun k => f.eval x (r,.inr (.inr (j,k)))) =
      (Packet.record (.equal n span p q))[j.val]?.getD 0) :
    (schema old D w).read ((asTape f).eval x) r = marked (.equal n span p q) := by
  have he : (schema old D w).read ((asTape f).eval x) r =
      List.ofFn (fun j : Fin 9 => (tags[j.val],value (fun k => f.eval x (r,.inr (.inr (j,k)))))) := by
    simp only [FrozenTape.Schema.read,schema,asTape,Frame.select_eval]
    rfl
  apply he.trans
  exact (congrArg (fun g : Fin 9 → ℕ => List.ofFn fun j : Fin 9 => (tags[j.val],g j)) (funext hr)).trans rfl

private theorem collect {T U : Type*} (l : List T) (p : T → Prop) [DecidablePred p] (g : T → U) :
    (l.filterMap fun r => if p r then some (g r) else none) = (l.filter fun r => decide (p r)).map g := by
  induction l with
  | nil => rfl
  | cons r l ih => by_cases h : p r <;> simp [h,ih]

variable [NeZero D] {m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n sites np C h : ℕ} (seed : S ↪ Fin n)
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
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
local notation3 "tape" => asTape prog
variable {x : σ → Bool} (rep : Represents (G e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
    (outputRows e p bin perm positive first q oldEdge seed) portID F x)
variable (mask : ∀ k, x (occupied k) = true ↔ k ∈ Set.range (outputRows e p bin perm positive first q oldEdge seed))

include rep mask in
omit [Fintype P] in
/-- Every enabled frozen hook belongs to an attained terminal site and therefore
has a true stable owner for all later rekeying steps. -/
theorem attained (r : Row old D) (active : (tape).eval x (.inl (r,.inl ())) = true) :
    ∃ (a : S) (t : Fin D × Bool), owner ((tape).eval x) r = (terminalIndex e seed F (a,t)).val := by
  rw [(asTape_owner prog x r).1] at active
  rw [native_enabled,mask] at active
  obtain ⟨z,hz,hsel⟩ := (bandCandidate_mem_iff e p bin perm oldEdge seed (if r.2.2 then 0 else 1)
    r.1 (some (r.2.1,true))).mp active
  have hk : (if r.2.2 then (0 : Fin 3) else 1).val < 2 := by cases r.2.2 <;> decide
  obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp (((selected_iff (m := m) p bin perm z
    (some (r.2.1,true))).mp (hsel.mpr hk)).1)
  let a := (perm r.2.1).symm s
  have hbin : bin z = some (perm r.2.1 a) := by rw [Equiv.apply_symm_apply]; exact hs
  let z' : {z : p.layout.Edge // bin z = some (perm r.2.1 a)} := ⟨z,hbin⟩
  let t := (r.2.1,if r.2.2 then positive z else !(positive z))
  have h := (matched_hook e seed F counts p bin perm positive first q oldSite oldEdge portID cell aux rep a r.2.1 z' r.2.2).1
  have hrow : (oldEdge z'.val,r.2.1,r.2.2) = r := Prod.ext hz rfl
  rw [hrow] at h
  have ho := (exists_frame e seed F counts cut occupied).choose_spec.2 x r
  exact ⟨a,t,(asTape_owner prog x r).2.trans ((congrArg value (funext ho.2.1)).trans h)⟩

include rep mask in
omit [Fintype P] in
/-- A stable owner outside the actual terminal rectangle collects no hook records. -/
theorem outside (key : ℕ) (hk : ∀ a t,(terminalIndex e seed F (a,t)).val ≠ key) :
    (schema old D w).atSite ((tape).eval x) key = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro r _
  by_cases active : (tape).eval x (.inl (r,.inl ())) = true
  · obtain ⟨a,t,he⟩ := attained e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID cell aux
      rep mask r active
    simp [active,he,hk]
  · simp [active]

include rep mask in
omit [Fintype P] in
/-- Each enabled owner word names a genuine site of the physical successor. -/
theorem owners (r : Row old D) (active : (tape).eval x (.inl (r,.inl ())) = true) :
    ∃ v : (G₀).Site, owner ((tape).eval x) r = (F.sites (sID v)).val := by
  obtain ⟨a,t,he⟩ := attained e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID cell aux
    rep mask r active
  exact ⟨seedSite e p bin perm positive first q a (.inr (.inl t)),he⟩

include rep mask in
omit [Fintype P] in
/-- An old site, an inserted origin, or a paid site has an empty hook tape. -/
theorem at_other (v : (G₀).Site) (hv : ∀ a t,v ≠ seedSite e p bin perm positive first q a (.inr (.inl t))) :
    (schema old D w).atSite ((tape).eval x) (F.sites (sID v)).val = [] := by
  apply outside e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID cell aux rep mask
  intro a t h
  apply hv a t
  exact (sID).injective (F.sites.injective (Fin.ext h.symm))

include rep mask in
/-- Extracting an attained terminal by its true stable owner recovers its complete
marked hook block. The sparse-order premise holds on every saved dense layout by
`InheritedHook.eligible_sparse_order`. -/
theorem at_terminal (room : ∀ v,incoming G₀ v < 2^w) (names : S → ℕ) (a : S) (t : Fin D × Bool)
    (order : (eligible p bin perm a t.1).Pairwise (fun u v => oldEdge u.val < oldEdge v.val))
    (hone : 1 < 2^w) (hcount : value (fun k => counts.eval x (a,none,k)) = blocks p.layout bin perm m a)
    (hcut : ∀ z : {z : p.layout.Edge // bin z = some (perm t.1 a)}, ∀ col,
      value (fun k => cut.eval x ((oldEdge z.val,some (t.1,true)),col,k)) =
        CutCircuit.Result.read (descriptor p.layout bin perm m names z (some (t.1,true))) col)
    (fit : ∀ z : {z : p.layout.Edge // bin z = some (perm t.1 a)},
      Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*blocks p.layout bin perm m a +
        incoming G₀ ((G₀).dst (seedHook e p bin perm a t.1 z (decide (positive z.val = t.2)))) +
        count p.layout bin (perm t.1 a) < 2^w) :
    (schema old D w).atSite ((tape).eval x) (terminalIndex e seed F (a,t)).val =
      (InheritedProfile.hookRows e p bin perm positive first q a sID eID portID names t).map marked := by
  let Z := {z : p.layout.Edge // bin z = some (perm t.1 a)}
  let atSlot : Z ↪ Fin old := (Function.Embedding.subtype _).trans oldEdge
  let src (z : Z) := decide (positive z.val = t.2)
  let test (r : Row old D) := (tape).eval x (.inl (r,.inl ())) = true ∧
    owner ((tape).eval x) r = (terminalIndex e seed F (a,t)).val
  let read := (schema old D w).read ((tape).eval x)
  have hp (r : Row old D) : decide (test r) = true ↔ ∃ z ∈ eligible p bin perm a t.1, r = (atSlot z,t.1,src z) := by
    rw [decide_eq_true_eq]
    have hh := terminal_rows e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID cell aux
      rep mask a t r
    unfold test
    rw [(asTape_owner prog x r).1,(asTape_owner prog x r).2]
    apply hh.trans
    exact ⟨fun ⟨z,hz⟩ => ⟨z,by simp [eligible],hz⟩,fun ⟨z,_,hz⟩ => ⟨z,hz⟩⟩
  have hf := filtered (eligible p bin perm a t.1) atSlot t.1 src (fun r => decide (test r)) hp order
  change ((rows old D).filterMap (fun r => if test r then some (read r) else none)) = _
  refine (collect (rows old D) test read).trans ((congrArg (List.map read) hf).trans ?_)
  unfold InheritedProfile.hookRows
  rw [List.map_map,List.map_map]
  apply List.map_congr_left
  intro z _
  have hr := (native_live e seed F counts cut occupied p bin perm positive first q oldSite oldEdge portID cell aux rep room
    names a t.1 z (src z) hcount (hcut z) hone (fit z)).2
  exact read_equal prog x (atSlot z,t.1,src z) _ _ _ _ hr

end Packing.Inherited.HookTape

end BorderVNP
end Computability
end OAI
