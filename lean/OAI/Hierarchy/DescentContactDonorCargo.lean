import OAI.Hierarchy.DescentContactDonorSelection

namespace OAI
/-! # The two returned public-contact fields on the same old signed window -/
namespace Hierarchy.DescentContactDonorCargo
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {N a b H G M w : ℕ}

theorem fold_fits (table : Tables) (prior : Fin N→Expr) (keys : List (Fin N)) (out w : ℕ)
    (shift : table.shift.Fits w out) (applyRoom : table.apply.Fits w out)
    (held : ∀j,(prior j).Fits w out) :
    (DescentFirstContactPayload.exprOn table prior keys).Fits w out := by
  induction keys with
  | nil => trivial
  | cons j tail ih => exact ⟨applyRoom,ih,shift,held j⟩

/-- A single expression reads any two existing tables at their declared addresses. This allows
one match table per socket and one common first-donor table to be shared by all output blocks. -/
theorem fold_source (matchTable firstTable : Tables) (requested : ℕ)
    (own cargo : Fin N→Expr) (out : ℕ) (m : Memory w)
    (labels : Fin N→Fin H→Fin G→Cell a) (contents : Fin N→Fin H→Fin G→Cell b)
    (held : ∀j,DescentPackedZip.Fits matchTable (own j) (cargo j) a b M out w)
    (inputs : ∀j,Source (own j) (labels j) M m ∧ Source (cargo j) (contents j) M m)
    (matchBook : Static matchTable (DescentContactDonorSelection.keep (a:=a) (b:=b) requested) M m)
    (firstShift : firstTable.shift.Fits w out) (firstApply : firstTable.apply.Fits w out)
    (shiftBits : firstTable.shift.bits=b*M) (applyBits : firstTable.apply.bits=(b+b)*M)
    (firstBook : Static firstTable (DescentFirstContactPayload.prefer (b:=b)) M m) :
    let e:=DescentFirstContactPayload.exprOn firstTable (fun j=>matchTable.read (own j) (cargo j)) (List.finRange N)
    e.Fits w out ∧ Source e (fun h g=>DescentContactDonorSelection.visits requested
      (fun j=>labels j h g) (fun j=>contents j h g)) M m := by
  let expr:=fun j=>matchTable.read (own j) (cargo j)
  let data:=fun (j : Fin N) (h : Fin H) (g : Fin G)=>DescentContactDonorSelection.keep requested (labels j h g) (contents j h g)
  have sub (j : Fin N) : (expr j).Fits w out ∧ Source (expr j) (data j) M m:=by
    have r:=held j
    exact ⟨⟨r.apply,r.right,r.shift,r.left⟩,read_data matchTable (own j) (cargo j) out r
      (DescentContactDonorSelection.keep requested) (by simp [DescentContactDonorSelection.keep]) m matchBook
      (labels j) (contents j) (inputs j).1 (inputs j).2⟩
  exact DescentFirstContactPayload.from_mounted firstTable expr data m out (List.finRange N)
    (fun j=>(sub j).1) (fun j=>(sub j).2) firstShift firstApply shiftBits applyBits firstBook

def previous (requested a b M base : ℕ) (own : Fin N→Expr) (cargo : Fin 2→Fin N→Expr) (t : Fin 2) :=
  DescentContactDonorSelection.inputs requested a b M base own (cargo t)

def selected (requested : ℕ) (own : Fin N→Fin H→Fin G→Cell a)
    (cargo : Fin 2→Fin N→Fin H→Fin G→Cell b) (t : Fin 2) (h : Fin H) (g : Fin G) :=
  DescentContactDonorSelection.visits requested (fun j=>own j h g) (fun j=>cargo t j h g)

/-- The two fields visit exactly the same first matching old signed donor when their empty
markers agree on that socket. An empty window returns zero for both fields. -/
theorem same_donor (requested : ℕ) (localWord : Fin N→Cell a) (left halo : Fin N→Cell b)
    (support : ∀j,(localWord j).val=requested→(left j=0 ↔ halo j=0)) :
    let payload:=fun cargo=>DescentContactDonorSelection.visits requested localWord cargo
    (payload left=0 ∧ payload halo=0) ∨
      ∃j,(localWord j).val=requested ∧ left j≠0 ∧ halo j≠0 ∧
        payload left=left j ∧ payload halo=halo j := by
  intro payload
  let test:=fun (j : Fin N)=>decide (DescentContactDonorSelection.keep requested (localWord j) (left j)≠0)
  have agree : (fun j=>decide (DescentContactDonorSelection.keep requested (localWord j) (halo j)≠0))=test:=by
    funext j
    by_cases hit : (localWord j).val=requested ∧ (localWord j).val≠0
    · simp only [test,DescentContactDonorSelection.keep,ite_eq_left hit]
      exact decide_eq_decide.mpr (not_congr (support j hit.1).symm)
    · simp only [test,DescentContactDonorSelection.keep,ite_eq_right hit]
  have lookup (cargo : Fin N→Cell b) :
      payload cargo=((List.finRange N).find? (fun j=>decide (DescentContactDonorSelection.keep requested
        (localWord j) (cargo j)≠0))).elim 0 (fun j=>DescentContactDonorSelection.keep requested (localWord j) (cargo j)) :=
    DescentFirstContactPayload.firstOn_find _ _
  have l:=lookup left
  have h:=lookup halo
  rw [agree] at h
  change payload left=((List.finRange N).find? test).elim _ _ at l
  cases pos : (List.finRange N).find? test with
  | none => exact Or.inl ⟨by simpa [pos] using l,by simpa [pos] using h⟩
  | some j =>
    have ltst : test j=true:=List.find?_some pos
    have selected : DescentContactDonorSelection.keep requested (localWord j) (left j)≠0:=of_decide_eq_true ltst
    by_cases hit : (localWord j).val=requested ∧ (localWord j).val≠0
    · have genuine : left j≠0:=by simpa only [DescentContactDonorSelection.keep,ite_eq_left hit] using selected
      exact Or.inr ⟨j,hit.1,genuine,fun hz=>genuine ((support j hit.1).mpr hz),
        by simpa only [pos,Option.elim_some,DescentContactDonorSelection.keep,ite_eq_left hit] using l,
        by simpa only [pos,Option.elim_some,DescentContactDonorSelection.keep,ite_eq_left hit] using h⟩
    · exact False.elim (selected (by simp only [DescentContactDonorSelection.keep,ite_eq_right hit]))

def code (requested a b M base H G w : ℕ) (own : Fin N→Expr) (cargo : Fin 2→Fin N→Expr) (out : Fin 2→Bank) :=
  let p:=previous requested a b M base own cargo
  let next:=DescentContactDonorSelection.afterBook a b M base
  let first:=(mount (DescentContactDonorSelection.pages requested a b M)
        (DescentContactDonorSelection.dictBits a b M) w base).seq
      (DescentFirstContactPayload.program (p 0) b M next (out 0).base H G w)
  first.seq (scan w (out 1).base (H*chunks G M) (DescentFirstContactPayload.expr (p 1) b M next))

def clock (requested a b M base H G : ℕ) (own : Fin N→Expr) (cargo : Fin 2→Fin N→Expr) :=
  let p:=previous requested a b M base own cargo
  let next:=DescentContactDonorSelection.afterBook a b M base
  ((4+10*(2*2^(DescentContactDonorSelection.dictBits a b M)))+DescentFirstContactPayload.ticks (p 0) b M H G)+
    (4+H*chunks G M*(2*(DescentFirstContactPayload.expr (p 1) b M next).work+4))

def afterRun (requested a b M base H G : ℕ) (own : Fin N→Expr) (cargo : Fin 2→Fin N→Expr)
    (out : Fin 2→Bank) (m : Memory w) :=
  let p:=previous requested a b M base own cargo
  let next:=DescentContactDonorSelection.afterBook a b M base
  let matched:=after (DescentContactDonorSelection.pages requested a b M)
    (DescentContactDonorSelection.dictBits a b M) base m
  let first:=DescentFirstContactPayload.afterRun (p 0) b M next (out 0).base H G matched
  image (out 1).base (H*chunks G M) (DescentFirstContactPayload.expr (p 1) b M next) first

/-- Both fields use the same printed match and first-live tables. Field zero holds the true
left joint and field one holds the one-based old halo port. Both inputs refer to the same
occupied old signed slots. The output includes the vacant lanes of the rectangle. -/
theorem run (requested : ℕ) (own : Fin N→Expr) (cargo : Fin 2→Fin N→Expr) (m : Memory w)
    (labels : Fin N→Fin H→Fin G→Cell a) (contents : Fin 2→Fin N→Fin H→Fin G→Cell b)
    (base : ℕ) (out : Fin 2→Bank) (ceiling : ℕ)
    (ownFits : ∀j,(own j).Fits w base) (held : ∀t j,(cargo t j).Fits w base)
    (ownRead : ∀j,Source (own j) (labels j) M m) (read : ∀t j,Source (cargo t j) (contents t j) M m)
    (separated : DescentFirstContactPayload.dictionaryEnd b M (DescentContactDonorSelection.afterBook a b M base)≤(out 0).base)
    (apart : (out 0).base+H*chunks G M≤(out 1).base) (room : (out 1).base+H*chunks G M<2^w)
    (fits : ∀t,(out t).Fits w ceiling) (space : ∀t,H*chunks G M≤(out t).size) :
    let dst:=afterRun requested a b M base H G own cargo out m
    (code requested a b M base H G w own cargo out).Exec m dst (clock requested a b M base H G own cargo) ∧
      (∀t,Reads (out t) (selected requested labels contents t) M dst ∧
        Source (.lookup (out t) .row) (selected requested labels contents t) M dst) ∧
      (∀addr,(addr<base ∨ DescentFirstContactPayload.dictionaryEnd b M
          (DescentContactDonorSelection.afterBook a b M base)≤addr)→
        (addr<(out 0).base ∨ (out 0).base+H*chunks G M≤addr)→
        (addr<(out 1).base ∨ (out 1).base+H*chunks G M≤addr)→dst addr=m addr) ∧
      CheapCode (code requested a b M base H G w own cargo out) := by
  intro dst
  let pg:=DescentContactDonorSelection.pages requested a b M
  let bits:=DescentContactDonorSelection.dictBits a b M
  let next:=DescentContactDonorSelection.afterBook a b M base
  let firstPages:=DescentFirstContactPayload.pages b M
  let firstBits:=DescentFirstContactPayload.pageBits b M
  let matcher:=DescentContactDonorSelection.book requested a b M base
  let pref:=DescentFirstContactPayload.book b M next
  let p:=previous requested a b M base own cargo
  let ex:=fun t : Fin 2=>DescentFirstContactPayload.expr (p t) b M next
  let tables:=after firstPages firstBits next (after pg bits base m)
  let rows:=H*chunks G M
  let left:=image (out 0).base rows (ex 0) tables
  have above : (out 1).base<2^w:=(Nat.le_add_right ..).trans_lt room
  have firstRoom : (out 0).base+rows<2^w:=apart.trans_lt above
  have firstBase : (out 0).base<2^w:=(Nat.le_add_right ..).trans_lt firstRoom
  have early : next≤(out 0).base:=(Nat.le_add_right ..).trans separated
  have sourceEarly : base≤(out 0).base:=(Nat.le_add_right ..).trans early
  have onward : (out 0).base≤(out 1).base:=(Nat.le_add_right ..).trans apart
  have one (t : Fin 2) :=DescentContactDonorSelection.run requested own (cargo t) m labels (contents t)
    base (out 0) ceiling (fun j=>⟨ownFits j,held t j⟩) (fun j=>⟨ownRead j,read t j⟩)
    separated firstRoom (fits 0) (space 0)
  obtain ⟨exec0,got0,_,frame0,cheap0⟩:=one 0
  -- Either expression has the same two physical dictionary images immediately before its scan.
  have loaded : Source (ex 1) (selected requested labels contents 1) M tables := by
    intro row'
    exact (ProtocolRAMGeneratedWrite.read_image (out 0).base rows (ex 1) tables
      (row H G M row')).symm.trans ((one 1).2.1 row')
  have ms : matcher.shift.Fits w (out 0).base :=bank_room pg bits base _ 0
    (DescentContactDonorSelection.page_fits ..) early firstBase
  have ma : matcher.apply.Fits w (out 0).base :=bank_room pg bits base _ 1
    (DescentContactDonorSelection.page_fits ..) early firstBase
  have fs : pref.shift.Fits w (out 0).base :=bank_room firstPages firstBits next _ 0
    (DescentFirstContactPayload.page_room ..) separated firstBase
  have fa : pref.apply.Fits w (out 0).base :=bank_room firstPages firstBits next _ 1
    (DescentFirstContactPayload.page_room ..) separated firstBase
  have expression : (ex 1).Fits w (out 0).base :=by
    apply fold_fits pref (p 1) (List.finRange N) _ _ fs fa
    exact fun j=>⟨ma,ProtocolRAMGeneratedWrite.fits_mono _ sourceEarly (held 1 j),ms,
      ProtocolRAMGeneratedWrite.fits_mono _ sourceEarly (ownFits j)⟩
  have still : Source (ex 1) (selected requested labels contents 1) M left :=fun v=>
    (eval_below _ _ tables left expression (fun x h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ x (.inl h))).trans (loaded v)
  have second : (scan w (out 1).base rows (ex 1)).Exec left dst (4+rows*(2*(ex 1).work+4)) :=
    scan_exec (out 1).base rows (ex 1) left
      (ProtocolRAMGeneratedWrite.fits_mono _ onward expression) room
  have values (t : Fin 2) : Reads (out t) (selected requested labels contents t) M dst :=by
    fin_cases t
    · intro v
      have within:=(row H G M v).isLt
      change (row H G M v).val<rows at within
      exact (ProtocolRAMGeneratedWrite.frame_image (out 1).base rows (ex 1) left _
        (.inl ((Nat.add_lt_add_left within _).trans_le apart))).trans (got0 v)
    · intro v
      exact (ProtocolRAMGeneratedWrite.read_image (out 1).base rows (ex 1) left (row H G M v)).trans (still v)
  let first := (mount pg bits w base).seq (DescentFirstContactPayload.program (p 0) b M next (out 0).base H G w)
  let firstTicks := (4+10*(2*2^bits))+DescentFirstContactPayload.ticks (p 0) b M H G
  refine ⟨@Procedure.Exec.then w first (scan w (out 1).base rows (ex 1)) m left dst
    firstTicks (4+rows*(2*(ex 1).work+4)) exec0 second,fun t=>⟨values t,source_column (out t) ceiling (fits t) _ _ (space t) (values t)⟩,
    ?_,cheap_seq cheap0 (@scan_cheap _ _ _ _)⟩
  intro addr dict frameL frameR
  exact (ProtocolRAMGeneratedWrite.frame_image (out 1).base rows (ex 1) left addr frameR).trans (frame0 addr dict frameL)

end
end Hierarchy.DescentContactDonorCargo

end OAI
