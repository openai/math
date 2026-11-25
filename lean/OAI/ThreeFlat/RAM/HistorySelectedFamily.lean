import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies
import OAI.ThreeFlat.Diagonal.ProgramDirectory

namespace OAI
/-! # The finite native history dispatcher at an actual seed, shrink, or refresh row -/
namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal Computability.VPVNP.BurstRAM PrivateRAM HistoryNodeDirectory.Selected Diagonal.TickWorkspace
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F]

/-- The body sees the incremented cursor. Its node address still denotes the
ordinal selected by the loop before that increment. -/
theorem nodeAddress_bumped {W : ℕ} (u : ℕ) (m : Memory W) (i : ℕ)
    (ctrl : base u 18<2^W) (step : i+1<2^W) (current : (cur (ownerData W u) m).val=i) :
    nodeAddress u (bump (ownerData W u) m)=base u 44+8*i := by
  let d:=ownerData W u
  have adr : (d 0).val=base u 18 := Fin.val_cast_of_lt ctrl
  have read : m (d 0).val=(i:Word W) := Fin.ext (current.trans (Fin.val_cast_of_lt (by omega)).symm)
  have next : ((bump d m) (base u 18)).val=i+1 := by
    rw [←adr]
    simp only [bump,writeMemory,ite_true,read]
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt step]
  change base u 44+8*(((bump d m) (base u 18)).val-1)=_
  rw [next,Nat.add_sub_cancel]

theorem bumped_outside {W : ℕ} (u : ℕ) (m : Memory W) (ctrl : base u 18<2^W)
    {a : ℕ} (outside : a≠base u 18) : bump (ownerData W u) m a=m a := by
  have r : ((ownerData W u) 0).val=base u 18:= Fin.val_cast_of_lt ctrl
  simp [bump,writeMemory,r,outside]

/-- Pointers include the full size of every earlier physical ROM page. -/
def shrinkFamily (B : PhysicalStage.Block F) (start height : ℕ) (i : Fin B.levels) : Family :=
  (shrinkGrid B i).family (gridStart B start height+
    (((List.ofFn (shrinkGrid B)).take i.val).map Grid.size).sum)

def refreshFamily (B : PhysicalStage.Block F) (start height : ℕ) : Family :=
  (refreshGrid B).family (gridStart B start height+((List.ofFn (shrinkGrid B)).map Grid.size).sum)

omit [Field F] [Fintype F] in
private theorem find_at (f : Family→Bool) (pre after : List (Grid F)) (g : Grid F) (start : ℕ)
    (skip : ∀ a∈pre,∀ n,f (a.family n)=false) (hit : ∀ n,f (g.family n)=true) :
    (familiesFrom start (pre++g::after)).find? f=some (g.family (start+(pre.map Grid.size).sum)) := by
  induction pre generalizing start with
  | nil=>simp [familiesFrom,hit]
  | cons a pre ih=>
    have hs:=skip a List.mem_cons_self start
    have tail:=ih (start+a.size) (fun b hb=>skip b (List.mem_cons_of_mem _ hb))
    simpa [familiesFrom,List.find?_cons,hs,Nat.add_assoc] using tail

/-- All fixed family tags are positive, so a seed always takes the default arm. -/
theorem select_seed {W : ℕ} (B : PhysicalStage.Block F) (start height u : ℕ) (m : Memory W)
    (seed : (m (nodeAddress u m)).val=0) :
    (families B start height).find? (matchesFamily u m)=none := by
  apply List.find?_eq_none.mpr
  intro g _ h
  have tag := (of_decide_eq_true h).1
  rw [seed] at tag
  cases hm : g.mode <;> simp [hm,kind] at tag

/-- Strictly increasing shrink degrees select one real shrink page. -/
theorem select_shrink {W : ℕ} (B : PhysicalStage.Block F) (start height u : ℕ) (m : Memory W)
    (i : Fin B.levels) (tag : (m (nodeAddress u m)).val=1)
    (ports : (m (stageAddress u m+48)).val=2^B.exponent i.val) :
    (families B start height).find? (matchesFamily u m)=some (shrinkFamily B start height i) := by
  let xs:=List.ofFn (shrinkGrid B)
  have hi : i.val<xs.length := by simp [xs]
  have span:=List.take_append_drop i.val xs
  rw [List.drop_eq_getElem_cons hi] at span
  have item : xs[i.val]=shrinkGrid B i := by simp [xs]
  rw [item] at span
  change (familiesFrom (gridStart B start height) (xs++[refreshGrid B])).find? _=_
  have split : xs++[refreshGrid B]=xs.take i.val++(shrinkGrid B i)::(xs.drop (i.val+1)++[refreshGrid B]) := by
    calc
      _=(xs.take i.val++shrinkGrid B i::xs.drop (i.val+1))++[refreshGrid B] :=
        congrArg (fun a=>a++[refreshGrid B]) span.symm
      _=_ := by rw [List.append_assoc];rfl
  rw [split]
  apply find_at
  · intro g hg n
    obtain ⟨k,hk,hgk⟩:=List.mem_iff_getElem.mp hg
    have ki : k< i.val := lt_of_lt_of_le hk (by simp [List.length_take])
    let j : Fin B.levels:=⟨k,ki.trans i.isLt⟩
    have row : (xs.take i.val)[k]=shrinkGrid B j := by simp [j,xs]
    rw [←hgk,row]
    change decide ((m (nodeAddress u m)).val=1 ∧ (m (stageAddress u m+48)).val=2^B.exponent j.val)=false
    rw [tag,ports]
    have ne : (2:ℕ)^B.exponent i.val≠2^B.exponent j.val := ne_of_gt (increasing_ports B ki)
    simp [ne]
  · intro n
    change decide ((m (nodeAddress u m)).val=1 ∧ (m (stageAddress u m+48)).val=2^B.exponent i.val)=true
    simp [tag,ports]

/-- The unique refresh family is reached after every shrink geometry has been skipped. -/
theorem select_refresh {W : ℕ} (B : PhysicalStage.Block F) (start height u : ℕ) (m : Memory W)
    (tag : (m (nodeAddress u m)).val=2) (ports : (m (stageAddress u m+48)).val=2^B.exponent B.levels) :
    (families B start height).find? (matchesFamily u m)=some (refreshFamily B start height) := by
  change (familiesFrom (gridStart B start height) (List.ofFn (shrinkGrid B)++[refreshGrid B])).find? _=_
  apply find_at
  · intro g hg n
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hg
    change decide ((m (nodeAddress u m)).val=1 ∧ _)=false
    simp [tag]
  · intro n
    change decide ((m (nodeAddress u m)).val=2 ∧ (m (stageAddress u m+48)).val=2^B.exponent B.levels)=true
    simp [tag,ports]

/-- The same native shrink constructor fixes the LUT table and the selected
ROM slot, after loading the node's kernel and stage pointers. -/
theorem select_supported_shrink {W s D : ℕ} {T : ShrinkMotif.Table F} (B : PhysicalStage.Block F)
    (allowed : B.publicTemplate (.shrink s D T)) (start height u : ℕ) (m : Memory W)
    (kernel header : ℕ) (tag : (m (nodeAddress u m)).val=1)
    (toKernel : (m (nodeAddress u m+5)).val=kernel) (toStage : (m kernel).val=header)
    (degree : (m (header+48)).val=2^s) :
    ∃ i : Fin B.levels,s=B.exponent i.val ∧ D=2^B.exponent (i.val+1) ∧ T=B.shrink ∧
      (families B start height).find? (matchesFamily u m)=some (shrinkFamily B start height i) := by
  obtain ⟨i,es,ed,et⟩:=B.public_shrink allowed
  refine ⟨i,es,ed,et,select_shrink B start height u m i tag ?_⟩
  simpa only [stageAddress,toKernel,toStage,←es] using degree

private def staticExponent : PhysicalStage.StaticMotif F→ℕ
  | .shrink s ..=>s
  | .refresh s ..=>s

/-- Refresh reconstruction preserves the whole dependent graph/table term in
addition to the selected numerical guard. -/
theorem select_supported_refresh {W s h pad : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C : ℝ}
    {T : RefreshMotif.Table F c (1+h+pad) C} (B : PhysicalStage.Block F)
    (allowed : B.publicTemplate (.refresh s h pad c C T)) (start height u : ℕ) (m : Memory W)
    (kernel header : ℕ) (tag : (m (nodeAddress u m)).val=2)
    (toKernel : (m (nodeAddress u m+5)).val=kernel) (toStage : (m kernel).val=header)
    (degree : (m (header+48)).val=2^s) :
    PhysicalStage.StaticMotif.refresh s h pad c C T=.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh ∧
      (families B start height).find? (matchesFamily u m)=some (refreshFamily B start height) := by
  have actual:=B.public_refresh allowed
  have es : s=B.exponent B.levels:=congrArg staticExponent actual
  refine ⟨actual,select_refresh B start height u m tag ?_⟩
  simpa only [stageAddress,toKernel,toStage,←es] using degree

/-- Every static degree guard executes the same number of register operations. -/
def guardTicks (B : PhysicalStage.Block F) : ℕ :=
  2*(enabled 0 ((refreshGrid B).family 0)).work+4

omit [Field F] [Fintype F] in
private theorem family_length_aux (gs : List (Grid F)) (start : ℕ) :
    (familiesFrom start gs).length=gs.length := by
  induction gs generalizing start with
  | nil=>rfl
  | cons g gs ih=>simp [familiesFrom,ih]

theorem family_length (B : PhysicalStage.Block F) (start height : ℕ) :
    (families B start height).length=B.levels+1 := by
  simp [families,family_length_aux,grids]

omit [Fintype F] in
private theorem find_cost (B : PhysicalStage.Block F) {W : ℕ} (u : ℕ) (m : Memory W)
    (seed : ℕ) (arm : Family→ℕ) (fs : List Family) :
    bodyCost u m seed arm fs≤fs.length*guardTicks B+((fs.find? (matchesFamily u m)).map arm).getD seed := by
  induction fs with
  | nil=>simp [bodyCost]
  | cons f fs ih=>
    have step : 2*(enabled u f).work+4=guardTicks B := rfl
    cases key : matchesFamily u m f <;>
      simp [bodyCost,key,Nat.succ_mul] <;> omega

/-- All rejected table guards are already charged to this fixed block factor;
only the selected real body contributes its variable site work. -/
theorem selection_cost (B : PhysicalStage.Block F) (start height : ℕ) {W : ℕ} (u : ℕ) (m : Memory W)
    (seed : ℕ) (arm : Family→ℕ) :
    bodyCost u m seed arm (families B start height)≤(B.levels+1)*guardTicks B+
      (((families B start height).find? (matchesFamily u m)).map arm).getD seed := by
  simpa only [family_length] using find_cost B u m seed arm (families B start height)

omit [Field F] [Fintype F] in
private theorem roster_tag (start : ℕ) (gs : List (Grid F)) (f : Family)
    (mem : f∈familiesFrom start gs) : ∃g∈gs,f.oldPorts=g.oldPorts := by
  induction gs generalizing start with
  | nil=>simp [familiesFrom] at mem
  | cons g tail ih=>
    change f∈g.family start::familiesFrom (start+g.size) tail at mem
    rcases List.mem_cons.mp mem with h|h
    · exact ⟨g,List.mem_cons_self,by rw [h];rfl⟩
    · obtain ⟨a,ha,e⟩:=ih _ h
      exact ⟨a,List.mem_cons_of_mem _ ha,e⟩

/-- Every installed comparison literal fits once the final block degree fits. -/
theorem family_ports_bound (B : PhysicalStage.Block F) (start height : ℕ) (f : Family)
    (mem : f∈families B start height) : f.oldPorts≤2^B.exponent B.levels := by
  obtain ⟨g,hg,eqg⟩:=roster_tag (gridStart B start height) (grids B) f mem
  rw [eqg]
  rcases List.mem_append.mp hg with shrink|refresh
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp shrink
    exact (increasing_ports B).monotone j.isLt.le
  · simp only [List.mem_singleton] at refresh
    subst g
    exact le_rfl

open NavigationDirectory in
/-- The fixed program directory identifies the exact finite-table arm for an
actual archived positive stage. Both tag and old degree are read from memory. -/
theorem select_stage {W : ℕ} (B : PhysicalStage.Block F) (n rem oldBase start height u : ℕ)
    (m : Memory W) (q : Stage) (member : q∈(B.repeat n).directory rem oldBase)
    (K : ℕ) (c : Cursor)
    (tag : (m (nodeAddress u m)).val=(match q with | .shrink _=>1 | .refresh ..=>2))
    (degree : (m (stageAddress u m+48)).val=(allocate K c q).words 48) :
    match q with
    | .shrink x => ∃ i : Fin B.levels,x.oldDegree=2^B.exponent i.val ∧
        (families B start height).find? (matchesFamily u m)=some (shrinkFamily B start height i)
    | .refresh .. => (families B start height).find? (matchesFamily u m)=some (refreshFamily B start height) := by
  have support:=B.directory_family_degree n rem oldBase q member
  rw [family_degree] at degree
  cases q with
  | shrink x=>
    obtain ⟨i,ports⟩:=support
    exact ⟨i,ports,select_shrink B start height u m i tag (degree.trans ports)⟩
  | refresh v ports l h pad=>exact select_refresh B start height u m tag (degree.trans support)

open NavigationDirectory in
/-- Header column 48 in the chronological tape, at the precise word reached
by the S44 node's kernel pointer. -/
theorem directory_degree_read {W : ℕ} (K u : ℕ) (pre post : List Stage) (q : Stage) (c : Cursor)
    (m : Memory W) (address : stageAddress u m=c.header+64*pre.length)
    (atWord : (m (c.header+(64*pre.length+48))).val=
      ((tape K (pre++q::post) c)[64*pre.length+48]?).getD 0) :
    (m (stageAddress u m+48)).val=(allocate K (finish K pre c) q).words 48 := by
  have entry:=tape_header K pre q post c (⟨48,by decide⟩:Fin 64)
  change ((tape K (pre++q::post) c)[64*pre.length+48]?)=some ((allocate K (finish K pre c) q).words 48) at entry
  rw [address,Nat.add_assoc,atWord,entry];rfl


end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
