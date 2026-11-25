import OAI.Hierarchy.DescentFirstContactPayload

namespace OAI
/-! # A reached signed window supplies the first actual donor at a public socket -/
namespace Hierarchy.DescentContactDonorSelection
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM DescentFirstContactPayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {N a b H G M w : ℕ}

/-- Both the sender's label and returned payload are short. Zero denotes a vacant signed slot. -/
def keep (requested : ℕ) (own : Cell a) (cargo : Cell b) : Cell b :=
  if own.val=requested ∧ own.val≠0 then cargo else 0

def visits (requested : ℕ) (own : Fin N→Cell a) (cargo : Fin N→Cell b) : Cell b :=
  first (fun j=>keep requested (own j) (cargo j))

theorem found (requested : ℕ) (own : Fin N→Cell a) (cargo : Fin N→Cell b) (expected : Cell b)
    (positive : requested≠0) (seen : ∃j,(own j).val=requested ∧ cargo j≠0)
    (agree : ∀j,(own j).val=requested→cargo j=expected) :
    visits requested own cargo=expected := by
  apply first_agrees
  · obtain ⟨j,hit,live⟩:=seen
    exact ⟨j,by simpa [keep,hit,positive] using live⟩
  · intro j live
    by_cases hit : (own j).val=requested
    · simpa [keep,hit,positive] using agree j hit
    · simp [keep,hit] at live

def pages (requested a b M : ℕ) := binary (keep (a:=a) (b:=b) requested) M
def dictBits (a b M : ℕ) := (a+b)*M
def book (requested a b M base : ℕ) :=joined (pages requested a b M) (dictBits a b M) base id
def afterBook (a b M base : ℕ) := base+2*2^(dictBits a b M)
def inputs (requested a b M base : ℕ) (own cargo : Fin N→Expr) (j : Fin N) :=
  (book requested a b M base).read (own j) (cargo j)

theorem page_fits (requested a b M : ℕ) (j : Fin 2) : (pages requested a b M j).bits≤dictBits a b M:=by
  fin_cases j
  · exact Nat.mul_le_mul_right M (Nat.le_add_right _ _)
  · exact le_rfl

/-- Print the match table once, then apply the same two tables to all bounded old signed positions.
The same read accepts the opposite directed ticket, a source halo port, or a chronological donor ID. -/
theorem run (requested : ℕ) (own cargo : Fin N→Expr) (m : Memory w)
    (labels : Fin N→Fin H→Fin G→Cell a) (contents : Fin N→Fin H→Fin G→Cell b)
    (base : ℕ) (out : Bank) (ceiling : ℕ)
    (held : ∀j,(own j).Fits w base ∧ (cargo j).Fits w base)
    (read : ∀j,Source (own j) (labels j) M m ∧ Source (cargo j) (contents j) M m)
    (separated : DescentFirstContactPayload.dictionaryEnd b M (afterBook a b M base)≤out.base)
    (room : out.base+H*chunks G M<2^w) (fits : out.Fits w ceiling) (space : H*chunks G M≤out.size) :
    let pg:=pages requested a b M
    let d:=dictBits a b M
    let next:=afterBook a b M base
    let prev:=inputs requested a b M base own cargo
    let tail:=DescentFirstContactPayload.program prev b M next out.base H G w
    let dst:=DescentFirstContactPayload.afterRun prev b M next out.base H G (after pg d base m)
    let values:=fun h g=>visits requested (fun j=>labels j h g) (fun j=>contents j h g)
    ((mount pg d w base).seq tail).Exec m dst ((4+10*(2*2^d))+ticks prev b M H G) ∧
      Reads out values M dst ∧ Source (.lookup out .row) values M dst ∧
      (∀addr,(addr<base ∨ dictionaryEnd b M next≤addr)→(addr<out.base ∨ out.base+H*chunks G M≤addr)→dst addr=m addr) ∧
      CheapCode ((mount pg d w base).seq tail) := by
  intro pg d next prev tail dst values
  have enough : next≤out.base:=(Nat.le_add_right ..).trans separated
  have early : base≤next:=Nat.le_add_right ..
  have top : next<2^w:=enough.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run pg d base m top
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame pg d base m
  have pageLimit : ∀ j : Fin 2, (pg j).bits ≤ d := page_fits requested a b M
  have staticBook:=binary_mounted (keep (a:=a) (b:=b) requested) M pg d base m pageLimit id (fun _=>rfl)
  have l:=bank_room pg d base next 0 (pageLimit 0) le_rfl top
  have r:=bank_room pg d base next 1 (pageLimit 1) le_rfl top
  let items:=fun (j:Fin N) (h:Fin H) (g:Fin G)=>keep requested (labels j h g) (contents j h g)
  have atEach (j : Fin N) : (prev j).Fits w next ∧ Source (prev j) (items j) M (after pg d base m):=by
    have leftOK:=ProtocolRAMGeneratedWrite.fits_mono _ early (held j).1
    have rightOK:=ProtocolRAMGeneratedWrite.fits_mono _ early (held j).2
    have lk : DescentPackedZip.Fits (book requested a b M base) (own j) (cargo j) a b M next w:=
      ⟨leftOK,rightOK,l,r,rfl,rfl⟩
    refine ⟨?_,read_data _ _ _ next lk _ (by simp [keep]) _ staticBook _ _ ?_ ?_⟩
    · change ((book requested a b M base).read (own j) (cargo j)).Fits w next
      simp [Tables.read,Expr.Fits,lk.apply,lk.shift,leftOK,rightOK]
    · exact fun pos=>(eval_below _ _ m _ (held j).1 (fun x lo=>frame x (.inl lo))).trans ((read j).1 pos)
    · exact fun pos=>(eval_below _ _ m _ (held j).2 (fun x lo=>frame x (.inl lo))).trans ((read j).2 pos)
  obtain ⟨exec,got,source,rest,cheap⟩:=DescentFirstContactPayload.run prev _ items next out ceiling
    (fun j=>(atEach j).1) (fun j=>(atEach j).2) separated room fits space
  refine ⟨@Procedure.Exec.then w (mount pg d w base) tail m (after pg d base m) dst
    (4+10*(2*2^d)) (ticks prev b M H G) mounted.1 exec,
    got,source,?_,cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap pg d w base) cheap⟩
  intro addr outside away
  rcases outside with lo|hi
  · exact (rest addr (.inl (lo.trans_le early)) away).trans (frame addr (.inl lo))
  · exact (rest addr (.inr hi) away).trans (frame addr (.inr ((Nat.le_add_right ..).trans hi)))

end
end Hierarchy.DescentContactDonorSelection

end OAI
