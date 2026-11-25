import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # The original or fixed-template source of every private birth box

Every saved output host is either a retained input host or was created by a
real subdivision or paid sewing step. A fresh relay, origin or terminal has
no factor box. A fresh paid host has precisely the singleton one-copy factor
of its designated site in the fixed paid identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option maxRecDepth 2200

variable {D m : ℕ} {K : Type} [Field K] (e : PaidIdentity K D m) (number : e.Entry → ℕ)

/-- The complete list of boxes permitted at a newly born host of a physical step. -/
def FreshBoxes (s : Site) : Prop :=
  s.boxes = [] ∨ ∃ a : Fin e.count, ∃ v : (e.net a).Site, s.boxes = [[PaidBox.tableFactor e number a v]]

/-- The intrinsic program at a new host reads only its own finite bank.
Its factor list records whether the host contributes a paid table. -/
def FreshBirth (s : Site) : Prop := s.Local ∧ FreshBoxes e number s

variable {k d d' : ℕ} [NeZero D] {P I B : Type} [Fintype P] [Fintype I] [Fintype B]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (q : s.Index e) (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : (Fin k × P) ↪ Fin np)
    (seed : ((I → Deck (d'+1)) × B) → ℕ)

namespace Stage

/-- Classify every output site of one selected normalized crossing, before the second
cable sort. The returned old host is the real child at the indicated parallel address. -/
theorem privateBirthCases (v : (s.result e q).pack.layout.Site) :
    (∃ u, (normalizedStage e s q).site u = v) ∨
      FreshBirth e number (s.privatePrograms e q old siteID edgeID portID seed number v).birth := by
  rcases v with u | ⟨b,(_ | _ | ⟨a,v⟩)⟩
  · exact .inl ⟨u,rfl⟩
  · exact .inr ⟨InheritedProfile.origin_local e s.input s.label s.perm s.orient (0,false) q b siteID edgeID portID,.inl rfl⟩
  · exact .inr ⟨InheritedProfile.terminal_local e s.input s.label s.perm s.orient (0,false) q b siteID edgeID portID seed _,.inl rfl⟩
  · exact .inr ⟨PaidSite.physical_local e s.input s.label s.perm s.orient (0,false) q b a v edgeID portID number,
      .inr ⟨a,v,rfl⟩⟩

end Stage

namespace Program

variable {rounds : ℕ} {A : ℕ → Type*} {Bin : Fin rounds → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e} (F : Program (B := Bin) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- The second dense cable save transports the same classification to the state's
actual stable host. Its fresh boxes are still those of the selected public step. -/
theorem savePrivateBirthCases (i : Fin rounds) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (v : (view (i.val+1) (F.advance i c q)).pack.layout.Site) :
    (∃ u, (F.siteStorage store i c q).site ((normalizedStage e (F.stage i c) q).site u) = v) ∨
      FreshBirth e number (F.savePrivatePrograms store rows number i c q old v).birth := by
  let st := F.stage i c
  let next := st.privatePrograms e q old (rows.sites i c q) (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number
  obtain ⟨w,rfl⟩ := (F.siteStorage store i c q).site.surjective v
  rcases st.privateBirthCases e number q old _ _ _ _ w with ⟨u,he⟩ | h
  · exact .inl ⟨u,congrArg (F.siteStorage store i c q).site he⟩
  · exact .inr ((congrArg (FreshBirth e number)
      (carryPrivatePrograms_birth _ _ _ _ next w)).mpr h)

/-- Every actual normalized histogram site outside its retained original-host map
has an empty or fixed paid box table. -/
theorem replayPrivateBirthCases (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (q : (F.system.histories n hn a).Index) (v : (view n (RowTrace.state F.system n hn a q)).pack.layout.Site) :
    (∃ u, (normalizedAncestry F (F.siteStorage store) n hn a q).site u = v) ∨
      FreshBirth e number (F.replayPrivatePrograms store rows number n hn a initial q v).birth := by
  induction n with
  | zero => exact .inl ⟨v,rfl⟩
  | succ n ih =>
    let hl := Nat.lt_of_succ_le hn
    let i : Fin rounds := ⟨n,hl⟩
    let c := fun j : Fin k => RowTrace.state F.system n hl.le (a j) (q.1 j)
    let children := fun j : Fin k => (parallelLeaves (fun x => (view 0 x).pack) n (a j)).layout
    let src (j : Fin k) (w : (children j).Site) := (initial ⟨j,w⟩).castWidth
      ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq children j w))
    let old := fun j : Fin k => F.replayPrivatePrograms store rows number n hl.le (a j) (src j) (q.1 j)
    rcases F.savePrivateBirthCases store rows number i c q.2 old v with ⟨⟨j,w⟩,rfl⟩ | h
    · rcases ih hl.le (a j) (src j) (q.1 j) w with ⟨u,rfl⟩ | h
      · exact .inl ⟨⟨j,u⟩,rfl⟩
      · exact .inr ((congrArg (FreshBirth e number) (F.savePrivatePrograms_birth store rows number i c q.2 old ⟨j,w⟩)).mpr h)
    · exact .inr h

/-- For a whole inner epoch with row-major flat original leaf addresses. -/
theorem flatPrivateBirthCases (flat : Fin (k^rounds) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout) (q : F.Hist flat)
    (v : (flattenPack rounds (F.terminal flat q).pack).layout.Site) :
    (∃ u, (normalizedHosts F (namesStorage F store) flat q).site u = v) ∨
      FreshBirth e number (F.flatPrivatePrograms store rows number flat initial q v).birth := by
  let leaf := fun z => (view 0 z).pack
  let src := nestedPrivatePrograms leaf rounds flat initial
  rcases F.replayPrivateBirthCases store rows number rounds le_rfl (leavesEquiv k _ rounds flat) src q v with ⟨u,rfl⟩ | h
  · refine .inl ⟨originalNames leaf rounds flat u,?_⟩
    exact congrArg (normalizedAncestry F (F.siteStorage store) rounds le_rfl (leavesEquiv k _ rounds flat) q).site
      ((originalNames leaf rounds flat).symm_apply_apply u)
  · exact .inr h

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
