import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Selecting the first occupied donor in each packed contact window -/

namespace Hierarchy.DescentFirstContactPayload

open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {n b H G M w : ℕ}

def prefer (x y : Cell b) : Cell b := if x=0 then y else x

def firstOn (items : Fin n→Cell b) : List (Fin n)→Cell b
  | [] => 0
  | i::is => prefer (items i) (firstOn items is)

def first (items : Fin n→Cell b) : Cell b := firstOn items (List.finRange n)

theorem firstOn_eq_zero (items : Fin n→Cell b) (is : List (Fin n)) :
    firstOn items is=0 ↔ ∀i∈is,items i=0 := by
  induction is with
  | nil => simp [firstOn]
  | cons i is ih =>
    by_cases empty : items i=0 <;> simp [firstOn,prefer,empty,ih]

theorem first_eq_zero (items : Fin n→Cell b) : first items=0 ↔ ∀i,items i=0 := by
  simp only [first,firstOn_eq_zero,List.mem_finRange,true_implies]

theorem firstOn_witness (items : Fin n→Cell b) (is : List (Fin n)) (hit : firstOn items is≠0) :
    ∃i∈is,items i≠0 ∧ firstOn items is=items i := by
  induction is with
  | nil => exact (hit rfl).elim
  | cons i is ih =>
    by_cases empty : items i=0
    · have skipped : firstOn items (i::is)=firstOn items is:=by simp [firstOn,prefer,empty]
      obtain ⟨j,seen,live,chosen⟩:=ih (skipped ▸ hit)
      exact ⟨j,List.mem_cons_of_mem _ seen,live,skipped.trans chosen⟩
    · exact ⟨i,List.mem_cons_self,empty,by simp [firstOn,prefer,empty]⟩

theorem first_witness (items : Fin n→Cell b) (hit : first items≠0) :
    ∃i,items i≠0 ∧ first items=items i := by
  obtain ⟨i,_,live,chosen⟩:=firstOn_witness items (List.finRange n) hit
  exact ⟨i,live,chosen⟩

theorem first_agrees (items : Fin n→Cell b) (expected : Cell b)
    (seen : ∃i,items i≠0) (same : ∀i,items i≠0→items i=expected) : first items=expected := by
  obtain ⟨i,live⟩:=seen
  have hit : first items≠0:=fun blank=>live ((first_eq_zero items).mp blank i)
  obtain ⟨j,present,chosen⟩:=first_witness items hit
  exact chosen.trans (same j present)

/-- The literal donor order is retained for callers which attach a separate cargo to each visit. -/
theorem firstOn_find (items : Fin n→Cell b) (is : List (Fin n)) :
    firstOn items is=(is.find? (fun i=>decide (items i≠0))).elim 0 items := by
  induction is with
  | nil => rfl
  | cons i is ih => by_cases empty : items i=0 <;> simp [firstOn,prefer,empty,ih]

def pages (b M : ℕ) := binary (prefer (b:=b)) M
def pageBits (b M : ℕ) := (b+b)*M
def book (b M base : ℕ) := joined (pages b M) (pageBits b M) base id

theorem page_room (b M : ℕ) (j : Fin 2) : (pages b M j).bits≤pageBits b M := by
  fin_cases j
  · exact Nat.mul_le_mul_right M (Nat.le_add_right b b)
  · exact le_rfl

def exprOn (T : Tables) (prior : Fin n→Expr) : List (Fin n)→Expr
  | [] => .lit 0
  | i::is => T.read (prior i) (exprOn T prior is)

def expr (prior : Fin n→Expr) (b M base : ℕ) :=
  exprOn (book b M base) prior (List.finRange n)

theorem workOn (T : Tables) (prior : Fin n→Expr) (is : List (Fin n)) :
    (exprOn T prior is).work=1+(is.map (fun i=>(prior i).work)).sum+11*is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [exprOn,DescentPackedZip.work,ih,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

theorem work (prior : Fin n→Expr) (b M base : ℕ) :
    (expr prior b M base).work=1+(∑i,(prior i).work)+11*n := by
  rw [expr,workOn,←List.ofFn_eq_map,List.sum_ofFn,List.length_finRange]

/-- One mounted two-input table serves all donor positions and every active SIMD lane. -/
theorem from_mounted (T : Tables) (prior : Fin n→Expr) (items : Fin n→Fin H→Fin G→Cell b)
    (m : Memory w) (out : ℕ) (is : List (Fin n))
    (held : ∀i,(prior i).Fits w out) (sources : ∀i,Source (prior i) (items i) M m)
    (shift : T.shift.Fits w out) (applyRoom : T.apply.Fits w out)
    (shiftBits : T.shift.bits=b*M) (applyBits : T.apply.bits=(b+b)*M)
    (mounted : Static T (prefer (b:=b)) M m) :
    (exprOn T prior is).Fits w out ∧
      Source (exprOn T prior is) (fun h g=>firstOn (fun i=>items i h g) is) M m := by
  induction is with
  | nil =>
    refine ⟨trivial,?_⟩
    intro p
    change (0:Word w)=((data (fun _ : Fin H=>fun _ : Fin G=>(0:Cell b)) p).val:Word w)
    have blank : (data (fun _ : Fin H=>fun _ : Fin G=>(0:Cell b)) p).val=0 := by
      change (finFunctionFinEquiv (fun j : Fin M=>if _ : p.2.val*M+j.val<G then (0:Cell b) else 0)).val=0
      simp
    rw [blank,Nat.cast_zero]
  | cons i is ih =>
    have fit : DescentPackedZip.Fits T (prior i) (exprOn T prior is) b b M out w:=
      ⟨held i,ih.1,shift,applyRoom,shiftBits,applyBits⟩
    refine ⟨?_,DescentPackedZip.read_data T _ _ out fit prefer (by simp [prefer]) m mounted _ _ (sources i) ih.2⟩
    simp [exprOn,Tables.read,Expr.Fits,held i,ih.1,shift,applyRoom]

def dictionaryEnd (b M base : ℕ) := base+2*2^(pageBits b M)

def program (prior : Fin n→Expr) (b M base out H G w : ℕ) :=
  (mount (pages b M) (pageBits b M) w base).seq (scan w out (H*chunks G M) (expr prior b M base))

def afterRun (prior : Fin n→Expr) (b M base out H G : ℕ) (m : Memory w) :=
  image out (H*chunks G M) (expr prior b M base) (after (pages b M) (pageBits b M) base m)

def ticks (prior : Fin n→Expr) (b M H G : ℕ) :=
  (4+10*(2*2^(pageBits b M)))+(4+H*chunks G M*(2*(1+(∑i,(prior i).work)+11*n)+4))

theorem run (prior : Fin n→Expr) (m : Memory w) (items : Fin n→Fin H→Fin G→Cell b)
    (base : ℕ) (out : Bank) (ceiling : ℕ) (held : ∀i,(prior i).Fits w base)
    (sources : ∀i,Source (prior i) (items i) M m) (separated : dictionaryEnd b M base≤out.base)
    (room : out.base+H*chunks G M<2^w) (fits : out.Fits w ceiling) (space : H*chunks G M≤out.size) :
    let result:=fun h g=>first (fun i=>items i h g)
    let dst:=afterRun prior b M base out.base H G m
    (program prior b M base out.base H G w).Exec m dst (ticks prior b M H G) ∧
      Reads out result M dst ∧ Source (.lookup out .row) result M dst ∧
      (∀a,(a<base ∨ dictionaryEnd b M base≤a)→(a<out.base ∨ out.base+H*chunks G M≤a)→dst a=m a) ∧
      CheapCode (program prior b M base out.base H G w) := by
  intro result dst
  let span:=pageBits b M
  let pg:=pages b M
  let mid:=after pg span base m
  have sep : base+2*2^span≤out.base:=separated
  have early : base≤out.base:=(Nat.le_add_right ..).trans sep
  have upper : out.base<2^w:=(Nat.le_add_right ..).trans_lt room
  have start:=DescentOrdinaryAtomFieldRAM.ROM.run pg span base m (sep.trans_lt upper)
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame pg span base m
  have keep (i : Fin n) : Source (prior i) (items i) M mid:=fun p=>
    (eval_below _ _ m mid (held i) (fun j small=>frame j (.inl small))).trans (sources i p)
  have mounted:=binary_mounted (prefer (b:=b)) M pg span base m (page_room b M) id (fun _=>rfl)
  have read:=from_mounted (book b M base) prior items mid out.base (List.finRange n)
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ early (held i)) keep
    (bank_room pg span base out.base 0 (page_room b M 0) sep upper)
    (bank_room pg span base out.base 1 (page_room b M 1) sep upper) rfl rfl mounted
  have emit : (scan w out.base (H*chunks G M) (expr prior b M base)).Exec mid dst
      (4+H*chunks G M*(2*(expr prior b M base).work+4)) :=
    @scan_exec w out.base (H*chunks G M) (expr prior b M base) mid read.1 room
  have values : Reads out result M dst:=fun p=>
    (ProtocolRAMGeneratedWrite.read_image out.base _ _ mid (row H G M p)).trans (read.2 p)
  refine ⟨?_,values,source_column out ceiling fits _ result space values,?_,
    cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap pg span w base) (@scan_cheap _ _ _ _)⟩
  · have both : (program prior b M base out.base H G w).Exec m dst
        ((4+10*(2*2^span))+(4+H*chunks G M*(2*(expr prior b M base).work+4))) :=
      Procedure.Exec.then (A:=mount pg span w base)
        (B:=scan w out.base (H*chunks G M) (expr prior b M base)) start.1 emit
    have clock_eq : ticks prior b M H G =
        (4+10*(2*2^span))+(4+H*chunks G M*(2*(expr prior b M base).work+4)) := by
      simp only [ticks,span,work]
    rw [clock_eq]
    exact @both
  · intro a outside away
    exact (ProtocolRAMGeneratedWrite.frame_image out.base _ _ mid a away).trans (frame a outside)

end
end Hierarchy.DescentFirstContactPayload

end OAI
