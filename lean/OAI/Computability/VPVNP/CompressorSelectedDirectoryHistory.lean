import OAI.Computability.VPVNP.CompressorPlacementPersistence
import OAI.Computability.VPVNP.CompressorBlockMetadata
import OAI.Computability.VPVNP.PairTraversalControllerInputs

/-!
# Placement directories in the final memory of a selected branch

A pass publishes its preimage arrays and input-header fields in its own
level and advances the successor's DFS base and role. Replaying subsequent
passes preserves the completed levels, including the occurrence-specific
directory of each selected term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedDirectoryHistory

open BurstRAM Compression DescriptorSpace PairSimulation.LocalHistory
open PairSimulation.TraversalRows PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
/-- The input layer followed by the actual output layers in the accumulated branch. -/
noncomputable def layers (initial : TaggedLayer) (past : List (SelectedLevel B f hf)) : List TaggedLayer :=
  initial :: past.map fun v => ⟨levelLayer B f hf v,tagLevel B f hf v⟩

/-- The directory arrays and their native header words in one memory.
The upper bound for each array is the next level, even though the common
traversal limit is the start of the DFS arena. -/
structure Past (initial : TaggedLayer) (L : Layout) (base : ℕ) (past : List (SelectedLevel B f hf))
    (raw : Memory w) where
  /-- Placement directory of each previously selected level, as represented in the current raw
  memory. -/
  dirs : (i : Fin past.length) → LevelDirectory past[i] raw base
  within : ∀ i : Fin past.length, ((dirs i).pub 5).val + ((dirs i).pub 2).val*((dirs i).pub 4).val ≤
    levelStart L (i.val+1)
  lower : ∀ i : Fin past.length, levelsBase L ≤ ((dirs i).pub 1).val
  current : ∀ j ≤ past.length, raw (levelStart L j+14) = (layerBase B.recordLimit base (layers B f hf initial past) j : Word w)
  role : ∀ j : Fin (layers B f hf initial past).length, raw (levelStart L j.val+27) = ((layers B f hf initial past)[j].role.code : Word w)
  old : ∀ i : Fin past.length, raw (levelStart L i.val+21) = (dirs i).pub 0
  directory : ∀ i : Fin past.length, raw (levelStart L i.val+22) = (dirs i).pub 2 ∧
    raw (levelStart L i.val+24) = (dirs i).pub 3 ∧ raw (levelStart L i.val+25) = (dirs i).pub 5 ∧
    raw (levelStart L i.val+26) = (dirs i).pub 4

/-- Cardinality of the state where the next physical pass starts. -/
noncomputable def currentCount (initial : TaggedLayer) (past : List (SelectedLevel B f hf)) : ℕ :=
  ((layers B f hf initial past)[past.length]'(by simp [layers])).layer.count

/-- Past portion of the scheduled branch boundary. -/
def Prefix (initial : TaggedLayer) (L : Layout) (base : ℕ) (past : List (SelectedLevel B f hf))
    {a g : ℕ} (Y : State a g) (raw : Memory w) : Prop :=
  Nonempty (Past B f hf initial L base past raw) ∧ currentCount B f hf initial past = Y.positions

variable {B f hf} {L : Layout} {base : ℕ} {raw raw' : Memory w}

/-- The terminal prefix may write its own table and header after the
completed directory region. Only the first 28 words of the final level are
needed to retain the selected DFS headers. -/
noncomputable def Past.transport {initial : TaggedLayer} {past : List (SelectedLevel B f hf)}
    (D : Past B f hf initial L base past raw)
    (agree : ∀ x, levelsBase L ≤ x → x < levelStart L past.length + 28 → raw' x = raw x) :
    Past B f hf initial L base past raw' := by
  let ds (i : Fin past.length) := (D.dirs i).transport (m' := raw') (by
    intro x hx
    have ⟨hc,hr,_⟩ := (D.dirs i).regions
    have lower := D.lower i
    have upper := (D.within i).trans (levelStart_mono L i.isLt)
    rcases hx with hx|hx|hx <;> exact (agree x (by omega) (by omega)).symm)
  have read (j o : ℕ) (hj : j ≤ past.length) (ho : o < 28) :
      raw' (levelStart L j+o) = raw (levelStart L j+o) := by
    have lo : levelsBase L ≤ levelStart L j := Nat.le_add_right ..
    have hi := levelStart_mono L hj
    exact agree _ (by omega) (by omega)
  refine ⟨ds,D.within,D.lower,fun j hj => (read j 14 hj (by decide)).trans (D.current j hj),?_,
    fun i => (read i.val 21 i.isLt.le (by decide)).trans (D.old i),?_⟩
  · intro j
    have bound : j.val ≤ past.length := by
      simpa only [layers,List.length_cons,List.length_map,Nat.lt_succ_iff] using j.isLt
    exact (read j.val 27 bound (by decide)).trans (D.role j)
  · intro i
    obtain ⟨hn,hc,hr,hk⟩ := D.directory i
    exact ⟨(read i.val 22 i.isLt.le (by decide)).trans hn,(read i.val 24 i.isLt.le (by decide)).trans hc,
      (read i.val 25 i.isLt.le (by decide)).trans hr,(read i.val 26 i.isLt.le (by decide)).trans hk⟩


/-- Live scheduler and row-launcher writes below the level arena leave the
past-directory portion of the branch boundary intact. -/
theorem Prefix.transfer {a g : ℕ} {Y : State a g} {initial : TaggedLayer}
    {past : List (SelectedLevel B f hf)} (h : Prefix B f hf initial L base past Y raw)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) raw raw') : Prefix B f hf initial L base past Y raw' := by
  obtain ⟨⟨P⟩,count⟩ := h
  exact ⟨⟨P.transport fun x lo _ => (agree x (by simpa [levelStart] using lo)).symm⟩,count⟩

/-- The readback required at the completion of one native substep.
Its DFS prefix is advanced by the size of this input state; both words
written to the successor belong to the next pass's input header. -/
structure Emission (L : Layout) (i : ℕ) (v : SelectedLevel B f hf) (m out : Memory w) where
  /-- Placement directory published by the selected pass in its output memory, bounded by the
  next level's start. -/
  dir : LevelDirectory v out (levelStart L (i+1))
  lower : levelsBase L ≤ (dir.pub 1).val
  keepBase : out (levelStart L i+14) = m (levelStart L i+14)
  keepRole : out (levelStart L i+27) = m (levelStart L i+27)
  nextBase : out (levelStart L (i+1)+14) =
    m (levelStart L i+14) + ((B.recordLimit+2 : ℕ) : Word w)*(v.input.positions : Word w)
  nextRole : out (levelStart L (i+1)+27) = ((BlockMetadata.producingRole v.origin).code : Word w)
  old : out (levelStart L i+21) = dir.pub 0
  directory : out (levelStart L i+22) = dir.pub 2 ∧ out (levelStart L i+24) = dir.pub 3 ∧
    out (levelStart L i+25) = dir.pub 5 ∧ out (levelStart L i+26) = dir.pub 4

variable {initial : TaggedLayer} {past : List (SelectedLevel B f hf)} {v : SelectedLevel B f hf}

private structure Stored (L : Layout) (base i : ℕ) (v : SelectedLevel B f hf) (m : Memory w) where
  dir : LevelDirectory v m base
  within : (dir.pub 5).val+(dir.pub 2).val*(dir.pub 4).val ≤ levelStart L (i+1)
  lower : levelsBase L ≤ (dir.pub 1).val
  old : m (levelStart L i+21) = dir.pub 0
  directory : m (levelStart L i+22) = dir.pub 2 ∧ m (levelStart L i+24) = dir.pub 3 ∧
    m (levelStart L i+25) = dir.pub 5 ∧ m (levelStart L i+26) = dir.pub 4

/-- Initialize the DFS history from the published base and cursor role. -/
theorem Prefix.empty {a g : ℕ} {Y : State a g}
    (baseCell : raw (levelStart L 0+14) = (base : Word w))
    (roleCell : raw (levelStart L 0+27) = 0) :
    Prefix B f hf ⟨leafLayer (siteOrder Y),.cursor⟩ L base [] Y raw := by
  refine ⟨⟨⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,?_,
    fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩,?_⟩
  · intro j hj
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [layerBase_zero] using baseCell
  · intro j
    change Fin 1 at j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact roleCell
  · change (siteOrder Y).length = Fintype.card Y.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder Y).entries

private theorem layers_append (v : SelectedLevel B f hf) :
    layers B f hf initial (past++[v]) = layers B f hf initial past ++ [⟨levelLayer B f hf v,tagLevel B f hf v⟩] := by
  simp [layers]

/-- Extend the selected history by its actual pass. The new level can also
write the scheduler and the successor state. The proof only uses equality
on strictly earlier levels and the two carried words of its input header. -/
theorem Prefix.append (h : Prefix B f hf initial L base past v.input raw)
    (p : Emission L past.length v raw raw') (wide : 28 ≤ levelWords L)
    (room : levelStart L (past.length+1) ≤ base)
    (agree : ∀ x, levelsBase L ≤ x → x < levelStart L past.length → raw' x = raw x) :
    Prefix B f hf initial L base (past++[v]) (v.pass.next v.term) raw' := by
  obtain ⟨⟨P⟩,count⟩ := h
  let ls := layers B f hf initial past
  let newTag : TaggedLayer := ⟨levelLayer B f hf v,tagLevel B f hf v⟩
  have length : ls.length = past.length+1 := by simp [ls,layers]
  have here (j o : ℕ) (hj : j < past.length) (ho : o < 28) :
      raw' (levelStart L j+o) = raw (levelStart L j+o) := by
    have next := levelStart_mono L (show j+1 ≤ past.length from hj)
    have span : levelStart L j+levelWords L = levelStart L (j+1) := by
      simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
    exact agree _ (by unfold levelStart; omega) (by omega)
  have oldStored (j : Fin past.length) : Stored L base j.val past[j] raw' := by
    let d := (P.dirs j).transport (m' := raw') (by
      intro x hx
      have ⟨hc,hr,_⟩ := (P.dirs j).regions
      have lower := P.lower j
      have upper := (P.within j).trans (levelStart_mono L j.isLt)
      rcases hx with hx|hx|hx <;> exact (agree x (by omega) (by omega)).symm)
    obtain ⟨hn,hc,hr,hk⟩ := P.directory j
    exact ⟨d,P.within j,P.lower j,(here j.val 21 j.isLt (by decide)).trans (P.old j),
      (here j.val 22 j.isLt (by decide)).trans hn,(here j.val 24 j.isLt (by decide)).trans hc,
      (here j.val 25 j.isLt (by decide)).trans hr,(here j.val 26 j.isLt (by decide)).trans hk⟩
  let ds (j : Fin (past++[v]).length) : Stored L base j.val (past++[v])[j] raw' := by
    by_cases old : j.val < past.length
    · simp only [Fin.getElem_fin,List.getElem_append_left old]
      exact oldStored ⟨j.val,old⟩
    · have hi : j.val < past.length+1 := by simpa using j.isLt
      have eqn : j.val = past.length := by omega
      simp only [Fin.getElem_fin]
      rw [List.getElem_concat_length eqn j.isLt,eqn]
      exact ⟨{ p.dir with inputEnd := p.dir.inputEnd.trans room },p.dir.inputEnd,p.lower,p.old,p.directory⟩
  refine ⟨⟨⟨fun j => (ds j).dir,fun j => (ds j).within,fun j => (ds j).lower,?_,?_,
    fun j => (ds j).old,fun j => (ds j).directory⟩⟩,?_⟩
  · intro j hj
    have bound : j ≤ ls.length := by simpa only [length,List.length_append,List.length_singleton] using hj
    rw [layers_append]
    change _ = (layerBase B.recordLimit base (ls++[newTag]) j : Word w)
    rw [layerBase,List.take_append_of_le_length bound]
    change _ = (layerBase B.recordLimit base ls j : Word w)
    rcases lt_trichotomy j past.length with hj|rfl|hj
    · exact (here j 14 hj (by decide)).trans (P.current j hj.le)
    · exact p.keepBase.trans (P.current _ le_rfl)
    · have hj' : j = past.length+1 := by omega
      subst j
      let i : Fin ls.length := ⟨past.length,by omega⟩
      change ls[i].layer.count = v.input.positions at count
      exact p.nextBase.trans (by rw [P.current _ le_rfl,← count]; exact BlockMetadata.next_layerBase _ _ ls i)
  · intro j
    have jfit : j.val < (ls++[newTag]).length := by simpa only [layers_append] using j.isLt
    have index : (layers B f hf initial (past++[v]))[j] = (ls++[newTag])[j.val]'jfit :=
      by simp only [Fin.getElem_fin,layers_append]; rfl
    rw [index]
    by_cases old : j.val < ls.length
    · rw [List.getElem_append_left old]
      let i : Fin ls.length := ⟨j.val,old⟩
      rcases lt_or_eq_of_le (show j.val ≤ past.length by omega) with hj|hj
      · exact (here j.val 27 hj (by decide)).trans (P.role i)
      · exact (hj ▸ p.keepRole : raw' (levelStart L j.val+27) = raw (levelStart L j.val+27)).trans (P.role i)
    · have jle : j.val < ls.length+1 := by simpa using jfit
      have jeq : j.val = ls.length := by omega
      rw [List.getElem_concat_length jeq jfit,jeq,length,p.nextRole,BlockMetadata.producingRole_code]
  · simp only [currentCount,layers_append,List.length_append,List.length_singleton]
    rw [List.getElem_concat_length (by simp [layers])]
    exact levelLayer_count B f hf v

/-- A native report stream which writes only below the level arena or at
and above its own input level preserves every previously collected row. -/
theorem Prefix.append_reports (h : Prefix B f hf initial L base past v.input raw) (rs : List (Report w))
    (p : Emission L past.length v raw (after raw (eventLog rs))) (wide : 28 ≤ levelWords L)
    (room : levelStart L (past.length+1) ≤ base)
    (writes : SourceTransport.Writes (fun x => x < levelsBase L ∨ levelStart L past.length ≤ x) (eventLog rs)) :
    Prefix B f hf initial L base (past++[v]) (v.pass.next v.term) (after raw (eventLog rs)) :=
  h.append p wide room fun _ lo hi => SourceTransport.after_outside raw writes (by omega)

/-- Replay the first `j` packets, keeping their source boundaries. -/
private def snapshot {J : Type*} (m : Memory w) (ps : List (SourceWalk.Packet J w)) (j : ℕ) : Memory w :=
  after m (eventLog ((ps.take j).flatMap SourceWalk.Packet.reports))

private theorem chronological_at {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    {m : Memory w} {ps : List (SourceWalk.Packet J w)} (h : SourceWalk.Chronological source m ps)
    (i : Fin ps.length) :
    ps[i].input = snapshot m ps i.val ∧ source ps[i].stage ps[i].input ps[i].reports ∧
      ps[i].output = snapshot m ps (i.val+1) := by
  induction ps generalizing m with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    obtain ⟨rfl,src,tail⟩ := h
    cases i using Fin.cases with
    | zero => exact ⟨rfl,src,by simp [snapshot,SourceWalk.Packet.output]⟩
    | succ i =>
      have h := ih tail i
      simpa only [Fin.getElem_fin,Fin.val_succ,List.getElem_cons_succ,snapshot,List.take_succ_cons,
        List.flatMap_cons,SourceWalk.after_append,SourceWalk.Packet.output] using h


variable (B f hf)
variable {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)

local notation "vs" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z

/-- The accumulated directories of the actual selected execution. -/
abbrev Retained (L : Layout) (base : ℕ) (raw : Memory w) :=
  Past B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L base vs raw

variable {B f hf T hT X z}

/-- Transport the full selected execution through the terminal prefix. -/
noncomputable def Retained.transport (D : Retained B f hf T hT X z L base raw)
    (agree : ∀ x, levelsBase L ≤ x → x < levelStart L (vs).length + 28 → raw' x = raw x) :
    Retained B f hf T hT X z L base raw' := Past.transport D agree

open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

private theorem input_counts {a g b l : ℕ} {Y : State a g}
    (E : StateExecution A b l Y) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (o : PassOrigins B f hf E) (c : E.Choices) :
    let ls := collectLevels B f hf E W r o c
    ls.map (fun v => v.input.positions) ++ [(E.finalState c).positions] =
      Y.positions :: ls.map SelectedLevel.outputSites := by
  induction E with
  | done => rfl
  | more p tail ih =>
    exact congrArg (List.cons _) (ih c.1 (W.2 c.1) (r.2 c.1) (o.2 c.1) c.2)

private theorem tag_count (i : Fin (vs).length) :
    (tags[i.val]'(by simp only [selected,List.length_cons,List.length_map]; omega)).layer.count =
      vs[i].input.positions := by
  have e : (vs).map (fun v => v.input.positions) ++ [((B.execute f hf T hT X).finalState z).positions] =
      X.positions :: (vs).map SelectedLevel.outputSites := input_counts (B.execute f hf T hT X) _ _ _ z
  have h : (tags).map (fun l => l.layer.count) =
      X.positions :: (vs).map SelectedLevel.outputSites := by
    rw [← selected_layer_counts B f hf T hT X z,← selected_layers B f hf T hT X z,List.map_map]
    rfl
  have eq := congrArg (fun l : List ℕ => l[i.val]?) (h.trans e.symm)
  have hi : i.val < ((vs).map (fun v => v.input.positions)).length := by simp
  simpa only [List.getElem?_map,List.getElem?_append_left hi,List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem (show i.val < (tags).length by simp [selected]),
    Option.map_some,Option.some.injEq,Fin.getElem_fin] using eq

private theorem current_take (i : Fin (vs).length) :
    currentCount B f hf ⟨leafLayer (siteOrder X),.cursor⟩ ((vs).take i.val) = vs[i].input.positions := by
  have len := List.length_take_of_le i.isLt.le
  have pre : layers B f hf ⟨leafLayer (siteOrder X),.cursor⟩ ((vs).take i.val) = (tags).take (i.val+1) := by
    simp only [layers,selected,List.take_succ_cons,List.map_take]
  simpa only [currentCount,len,pre,List.getElem_take] using tag_count (B := B) (f := f) (hf := hf) (z := z) i

/-- A batch of native reports which emits the selected occurrence and frames
all earlier levels, including when it also updates the low scheduler words. -/
def Source (L : Layout) (i : Fin (vs).length) (m : Memory w) (rs : List (Report w)) : Prop :=
  Nonempty (Emission L i.val vs[i] m (after m (eventLog rs))) ∧
    SourceTransport.Writes (fun x => x < levelsBase L ∨ levelStart L i.val ≤ x) (eventLog rs)

/-- Extract every occurrence's directory at the final memory of the actual
report walk. Empty walks retain the cursor header. -/
noncomputable def ofWalk {rs : List (Report w)}
    (walk : SourceWalk (Source (B := B) (f := f) (hf := hf) (z := z) L) (List.finRange (vs).length) raw rs)
    (baseCell : raw (levelStart L 0+14) = (base : Word w))
    (roleCell : raw (levelStart L 0+27) = 0)
    (wide : 28 ≤ levelWords L) (room : levelStart L (vs).length ≤ base) :
    Retained B f hf T hT X z L base (after raw (eventLog rs)) := by
  apply Classical.choice
  obtain ⟨ps,stages,logs,chron⟩ := walk.packets
  let image := snapshot raw ps
  let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
  have size : ps.length = (vs).length := by
    simpa only [List.length_map,List.length_finRange] using congrArg List.length stages
  have accum (j : ℕ) (hj : j ≤ (vs).length) : Nonempty (Past B f hf initial L base ((vs).take j) (image j)) := by
    induction j with
    | zero => exact (Prefix.empty (B := B) (f := f) (hf := hf) (Y := X) baseCell roleCell).1
    | succ j ih =>
      let i : Fin (vs).length := ⟨j,hj⟩
      let q : Fin ps.length := ⟨j,size.symm ▸ hj⟩
      have stage : ps[q].stage = i := by
        have eqn := getElem_congr_coll (i := j) (w := by rw [List.length_map]; exact q.isLt) stages
        simp only [List.getElem_map,List.getElem_finRange] at eqn
        exact Fin.ext (congrArg Fin.val eqn)
      obtain ⟨start,src,finish⟩ := chronological_at chron q
      rw [stage,start] at src
      obtain ⟨⟨p⟩,writes⟩ := src
      have len : ((vs).take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
      have before : Prefix B f hf initial L base ((vs).take j) vs[i].input (image j) :=
        ⟨ih (Nat.le_of_lt hj),current_take i⟩
      have out := before.append_reports ps[q].reports (by rw [len]; exact p) wide
        (by rw [len]; exact (levelStart_mono L hj).trans room) (by rw [len]; exact writes)
      change after ps[q].input (eventLog ps[q].reports) = image (j+1) at finish
      rw [start] at finish
      change after (image j) (eventLog ps[q].reports) = image (j+1) at finish
      rw [List.take_succ_eq_append_getElem hj,← finish]
      exact out.1
  have finalMem : image (vs).length = after raw (eventLog rs) := by
    simp only [image,snapshot,← size,List.take_length,logs]
  simpa only [List.take_length,finalMem] using accum (vs).length le_rfl

end CompressorRecords.SelectedDirectoryHistory

end VPVNP
end Computability
end OAI
