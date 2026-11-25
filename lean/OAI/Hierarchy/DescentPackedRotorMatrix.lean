import OAI.Hierarchy.DescentPackedResetRotorRoles
import OAI.Hierarchy.DescentPackedLocalLookup
import OAI.Hierarchy.DescentGoodPortCoherence
import OAI.Hierarchy.DescentTrunkReadout
import OAI.Hierarchy.ProtocolRAMPurchaseSampler

namespace OAI
/-! # Forming the true installed good-base traffic matrix from bounded signed bundle rows -/
namespace Hierarchy.DescentPackedRotorMatrix
open DescentBaseProfile DescentChosenRouter DescentRouterSlots DescentSIMDLookup DescentRotor DescentPackedResetRotorRoles
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentPackedFallbackTree.Image
open scoped Classical BigOperators
noncomputable section
local notation "Y" n:arg => (2^n:ℕ)
def bits (n : ℕ) := 2*n+1
def bins (cap : ℕ) := ProtocolRAMPurchaseSampler.bits cap
def pair {n : ℕ} (a b : Fin (Y n)) : Cell (bits n) :=
  ⟨1+(finProdFinEquiv (a,b)).val,by
    have size : (2:ℕ)^n*2^n=2^(2*n) := by rw [two_mul,pow_add]
    have bound := lt_of_lt_of_eq (finProdFinEquiv (a,b)).isLt size
    rw [bits,pow_succ]
    omega⟩

@[simp] theorem pair_nonzero {n : ℕ} (i j : Fin (Y n)) : pair i j≠0 := by
  intro h
  have := congrArg Fin.val h
  change 1+_=0 at this;omega

@[simp] theorem pair_inj {n : ℕ} (i j k l : Fin (Y n)) : pair i j=pair k l ↔ i=k ∧ j=l := by
  constructor
  · intro h
    have same := congrArg Fin.val h
    change 1+_=1+_ at same
    exact Prod.mk.inj (finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel same)))
  · rintro ⟨rfl,rfl⟩;rfl

def rows (n J : ℕ) (x : Fin J→Cell (bits n)) := encode (bits n) J x
def tally (n J : ℕ) (input : Cell (bits n*J)) : Cell (bins J*(Y n*Y n)) :=
  encode (bins J) (Y n*Y n) (fun t=>
    let p:=finProdFinEquiv.symm t
    let hits:=Finset.univ.filter (fun r : Fin J=>(encode (bits n) J).symm input r=pair p.1 p.2)
    ⟨hits.card,by
      have count : hits.card ≤ J := by simpa only [Fintype.card_fin] using Finset.card_le_univ hits
      exact count.trans_lt (ProtocolRAMPurchaseSampler.lt_span J)⟩)

theorem tally_read {n J : ℕ} (x : Fin J→Cell (bits n)) (i j : Fin (Y n)) :
    matrix n (bins J) (tally n J (rows n J x)) i j=(Finset.univ.filter (fun t=>x t=pair i j)).card := by
  simp only [matrix,tally,rows,Equiv.symm_apply_apply]

variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k n d J : ℕ}
variable (P : Placement V I H A k (Y n)) (s : Bool) (g : P.Good)

theorem paid (e : Cells P s g) : useRotor P.b P.depth P.L P.keys P.hub P.old e.val :=
  (in_good_iff P.b P.depth P.L P.keys P.hub P.old P.ends P.span P.ticket P.fall s e.val).1 ⟨g,e.property⟩

theorem root_row (e : Cells P s g) : source P s g e=P.row s (P.old s e.val) := by
  rcases e with ⟨e,h⟩
  have enabled:=paid P s g ⟨e,h⟩
  simp [source,head,root,Placement.input,pub,first,enabled]; rfl

theorem link_column (book : P.ColumnRoster d) (e : Cells P s g) :
    (target P s g e).val=P.reservedColumn d book.host book.near book.size s (P.ticket ⟨e.val,paid P s g e⟩) := by
  rcases e with ⟨e,h⟩
  have enabled:=paid P s g ⟨e,h⟩
  let t:=P.ticket ⟨e,enabled⟩
  have hh : P.ends s t.1=g := by
    simpa [Placement.contact,contact,Placement.owner,owner,enabled,t] using h
  have selected (base : P.Good) (atBase : P.ends s t.1 = base) (z : Cells P s base)
      (hit : P.contact z.val = .inl t) : target P s base z = (P.outputName d s t).2 := by
    cases atBase
    have same : link P.contact P.owner s (.inl (P.ends s t.1)) z = ⟨.inl t,rfl⟩ :=
      Subtype.ext hit
    exact congrArg (fun l => tail P s (P.ends s t.1) l) same
  have hit : P.contact e = .inl t := by simp [Placement.contact,contact,enabled,t]
  exact (congrArg Fin.val (selected g hh ⟨e,h⟩ hit)).trans (book.read s t)

/-- One slot per surviving signed bundle in this good base. The read law below allows any bounded physical
slot directory and permits arbitrary gaps in it. -/
structure Roster (J : ℕ) where
  index : Cells P s g↪Fin J

def physical (roster : Roster P s g J) (q : Fin J) : Cell (bits n) :=
  if found : ∃e,roster.index e=q then
    let e:=found.choose
    pair (source P s g e) (target P s g e)
  else 0

@[simp] theorem physical_at (roster : Roster P s g J) (e : Cells P s g) :
    physical P s g roster (roster.index e)=pair (source P s g e) (target P s g e) := by
  have yes : ∃i,roster.index i=roster.index e:=⟨e,rfl⟩
  simp only [physical,dite_eq_left yes,roster.index.injective yes.choose_spec]

theorem physical_count (roster : Roster P s g J) (i j : Fin (Y n)) :
    matrix n (bins J) (tally n J (rows n J (physical P s g roster))) i j=
      matrixOfBundles (source P s g) (target P s g) i j := by
  rw [tally_read]
  unfold matrixOfBundles
  symm
  apply Finset.card_bij (fun e _=>roster.index e)
  · intro e he
    obtain ⟨a,b⟩:=(Finset.mem_filter.mp he).2
    simp [a,b]
  · intro a _ b _ eqn;exact roster.index.injective eqn
  · intro q hq
    have tag:=(Finset.mem_filter.mp hq).2
    by_cases yes : ∃e,roster.index e=q
    · obtain ⟨e,rfl⟩:=yes
      rw [physical_at,pair_inj] at tag
      exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,tag⟩,rfl⟩
    · have empty : physical P s g roster q=0 := dite_eq_right yes
      exact False.elim ((pair_nonzero i j) (tag.symm.trans empty))

/-- The matrix ROM only reads each locally reached true signed pair once as a short input digit. -/
theorem issued {hosts groups M w n cap : ℕ} (g : Banks) (out : ℕ)
    (signed : Fin hosts→Fin groups→Fin cap→Cell (bits n)) (positive : 0<M) (mem : Memory w)
    (fit : Fits g (bits n*cap) (bins cap*(Y n*Y n)) M hosts groups w out)
    (stat : resident (tally n cap) g hosts groups M mem)
    (input : ∀q : Row hosts groups M,mem (g.source.base+(row hosts groups M q).val)=
      (data (fun v j=>rows n cap (signed v j)) q).val) :
    let dst:=imageBank hosts groups M out g mem
    (program g out hosts groups M w).Exec mem dst (4+44*hosts*chunks groups M) ∧
    ∀v j,digit (bins cap*(Y n*Y n)) (lane j positive).val (dst (out+(row hosts groups M (position v j positive)).val)).val=
      (tally n cap (rows n cap (signed v j))).val := by
  obtain ⟨run,read,_,_⟩:=DescentPackedLocalLookup.compile g out (tally n cap) (fun v j=>rows n cap (signed v j))
    positive fit mem stat (by
      intro q
      rw [←input q]
      exact (Fin.cast_val_eq_self _).symm)
  refine ⟨?_,read⟩
  rw [Nat.mul_assoc 44 hosts (chunks groups M)]
  intro pcSize regSize publicSize machine
  exact run machine

open DescentSixParty DescentResetTrunks DescentResetAttachments
variable {F Pin : Type} [Field F] {a : ℕ} {bw : Pin→ℕ} {W : MarkedWorld F a Pin bw}
    {price ε : ℝ} {hh C Ht : ℕ} (Z : ResetInput W price ε hh C Ht) (T : ResetInput.Terminals Z)
local notation "R" => Z.placement

/-- The correct source coordinate is exposed at the actual old terminal of this signed edge. -/
theorem terminal_source (s : Bool) (g : (R).Good) (e : Cells R s g) :
    (T.code (T.home (ends W.graph s e.val))).2.2=some (source R s g e) := by
  rw [T.attach,T.source s e.val (paid R s g e),root_row]; rfl

/-- Numerals from the actual signed terminal, potential peer prefix and untampered old ticket.
Columns follow the installed relabelling of the base. -/
theorem terminal_pair (s : Bool) (g : (R).Good) (e : Cells R s g) :
    ∃i j : Fin (Y Z.n),
      (T.code (T.home (ends W.graph s e.val))).2.2=some i ∧
      j.val=(R).reservedColumn T.commonDepth T.columns.host T.columns.near T.columns.size s
          ((R).ticket ⟨e.val,paid R s g e⟩) ∧
      pair i j=pair (source R s g e) (target R s g e) :=
  ⟨_,_,terminal_source Z T s g e,link_column R s g T.columns e,rfl⟩

end
end Hierarchy.DescentPackedRotorMatrix

end OAI
