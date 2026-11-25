import OAI.Hierarchy.DescentResetHeaderPlacement
import OAI.Hierarchy.DescentResetWindowScope
import OAI.Hierarchy.DescentResetPublicCensus

namespace OAI
/-! # Comparing actual published reset headers in the physical source order -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open ResetInput.PublicCensus
open scoped Classical

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "rank" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "grp" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=grp)) rank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "header" => fun e=>tag ((Z).actualFields T vertex birth e)

def cell (u : (coarse).graph.Site) : Cell :=
  (((Z).rawHostRank T vertex ((Z).placed T u)).val,((Z).blockId T u).val)

theorem cell_injective : Function.Injective (cell B) := by
  intro u v eqn
  exact (Z).place_unique T (((Z).rawHostRank T vertex).injective (Fin.ext (congrArg Prod.fst eqn)))
    (Fin.ext (congrArg Prod.snd eqn))

def siteOrder (x : Cell) : ℕ :=
  ((x.2/2^k)*pitch rank+x.1)*2^k + x.2%2^k

/-- The native operands are the reported host and common block at this
endpoint. Division and remainder are fixed public coordinate projections. -/
theorem siteOrder_cell (u : (coarse).graph.Site) : siteOrder B (cell B u)=rawSite u := by
  change _=(groupRank (Fin.valEmbedding (n:=grp)) rank (B.raw.pos u))*2^k+(B.raw.block u).val
  obtain ⟨p,b⟩:=B.rawGeometry
  rw [p,b]
  rfl

theorem hostCell (u : (coarse).graph.Site) :
    let host:=Stage.home B.next.placement (hop u)
    (rank host.1.2,host.2.val+2^k*host.1.1.val)=cell B u := by
  dsimp only
  rw [named_home B u]
  apply Prod.ext
  · rfl
  have join:=congrArg Fin.val ((digits).symm_apply_apply ((Z).blockId T u))
  exact join

theorem header_cells (e : (coarse).graph.Edge) :
    (header e).src=cell B ((coarse).graph.src e) ∧ (header e).dst=cell B ((coarse).graph.dst e) ∧
    (header e).ordinal=((Z).installedResetOrdinal T vertex birth e).val := ⟨rfl,rfl,rfl⟩

theorem header_before (e f : (coarse).graph.Edge) :
    ResetInput.PublicCensus.earlier (siteOrder B) (header f) (header e)=decide (earlier B e f) := by
  have same : cell B ((coarse).graph.src e)=cell B ((coarse).graph.src f) ↔
      rawSite ((coarse).graph.src e)=rawSite ((coarse).graph.src f) :=
    ⟨fun eqn=>congrArg (rawSite) (cell_injective B eqn),
     fun eqn=>congrArg (cell B) ((rawSite).injective eqn)⟩
  unfold ResetInput.PublicCensus.earlier earlier
  rw [(header_cells B e).1,(header_cells B f).1,(header_cells B e).2.2,(header_cells B f).2.2,
    siteOrder_cell,siteOrder_cell]
  apply decide_eq_decide.mpr
  exact or_congr Iff.rfl (and_congr same Iff.rfl)

/-- Reconstruct the comparator key from the actual seven stored columns
and their sparse rectangular address. Presence and amount stay in the row. -/
def recordTag (id : ℕ) (row : Fin 7→ℕ) : Tag :=
  ⟨id,(row 1,row 3),(row 2,row 4),decide (row 6=1)⟩

theorem recordTag_read (e : (coarse).graph.Edge) :
    recordTag (((Z).installedResetOrdinal T vertex birth e).val) ((Z).actualRecord T vertex e)=header e := by
  simp [recordTag,ResetInput.actualRecord,ResetInput.actualFields,tag]

/-- Genuine cell components bound every intermediate comparison. The maximum
rank plus one bounds a host digit, and the word addressing an occupied common
block also covers both its high group and low block. -/
theorem cell_room (v : (coarse).graph.Site) :
    (cell B v).1<pitch rank ∧ (cell B v).2<2^(T).commonDepth ∧
      (cell B v).2/2^k<grp ∧ (cell B v).2%2^k<2^k ∧
      siteOrder B (cell B v)<grp*pitch rank*2^k := by
  let x:=cell B v
  have host : x.1<pitch rank :=
    Nat.lt_succ_of_le (Finset.le_sup (f:=fun h=>rank h) (Finset.mem_univ ((Z).placed T v)))
  have addr : x.2<2^(T).commonDepth := ((Z).blockId T v).isLt
  have high : x.2/2^k<grp := (digits ((Z).blockId T v)).1.isLt
  have low := Nat.mod_lt x.2 (Nat.two_pow_pos k)
  refine ⟨host,addr,high,low,?_⟩
  have pair : (x.2/2^k)*pitch rank+x.1<grp*pitch rank :=
    calc
      _ < (x.2/2^k+1)*pitch rank := by rw [Nat.succ_mul]; exact Nat.add_lt_add_left host _
      _ ≤ _ := Nat.mul_le_mul_right _ high
  change ((x.2/2^k)*pitch rank+x.1)*2^k+x.2%2^k<_
  calc
    _ < ((x.2/2^k)*pitch rank+x.1+1)*2^k := by rw [Nat.succ_mul];exact Nat.add_lt_add_left low _
    _ ≤ _ := Nat.mul_le_mul_right _ pair

private theorem digit_lt {a b x y radix : ℕ} (xRoom : x<radix) (yRoom : y<radix) :
    a*radix+x < b*radix+y ↔ a<b ∨ a=b ∧ x<y := by
  have grow {u v j l : ℕ} (up : u<v) (fit : j<radix) : u*radix+j<v*radix+l :=
    calc
      _ < (u+1)*radix := by rw [Nat.succ_mul];exact Nat.add_lt_add_left fit _
      _ ≤ v*radix := Nat.mul_le_mul_right _ up
      _ ≤ _ := Nat.le_add_right _ _
  rcases lt_trichotomy a b with before|eqn|after
  · exact iff_of_true (grow before xRoom) (.inl before)
  · subst b;simp
  · have reverse : b*radix+y<a*radix+x:=grow after yRoom
    simp [not_lt_of_gt reverse,not_lt_of_gt after,Ne.symm after.ne]

/-- Compare group, rectangular host and block in that order. No product with
a private pitch is necessary in the comparison instructions. -/
def cellLex (radixBits : ℕ) (x y : Cell) : Prop :=
  x.2/2^radixBits<y.2/2^radixBits ∨ x.2/2^radixBits=y.2/2^radixBits ∧
    (x.1<y.1 ∨ x.1=y.1 ∧ x.2%2^radixBits<y.2%2^radixBits)

private theorem order_lt (k stride : ℕ) (x y : Cell) (hx : x.1 < stride) (hy : y.1 < stride) :
    ((x.2/2^k)*stride+x.1)*2^k+x.2%2^k <
      ((y.2/2^k)*stride+y.1)*2^k+y.2%2^k ↔ cellLex k x y := by
  have compare := digit_lt (a:=x.2/2^k) (b:=y.2/2^k) hx hy
  have equalKey : (x.2/2^k)*stride+x.1=(y.2/2^k)*stride+y.1 ↔
      x.2/2^k=y.2/2^k ∧ x.1=y.1 := by
    constructor
    · intro same
      have rev:=digit_lt (a:=y.2/2^k) (b:=x.2/2^k) hy hx
      have nlt:=mt compare.mpr (not_lt_of_ge same.ge)
      have ngt:=mt rev.mpr (not_lt_of_ge same.le)
      omega
    · rintro ⟨hi,lo⟩;rw [hi,lo]
  change ((x.2/2^k)*stride+x.1)*2^k+x.2%2^k <
    ((y.2/2^k)*stride+y.1)*2^k+y.2%2^k ↔ _
  rw [digit_lt (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k)),compare,equalKey]
  change _ ↔ x.2/2^k<y.2/2^k ∨ x.2/2^k=y.2/2^k ∧
    (x.1<y.1 ∨ x.1=y.1 ∧ x.2%2^k<y.2%2^k)
  tauto

theorem siteOrder_lt (u v : (coarse).graph.Site) :
    siteOrder B (cell B u)<siteOrder B (cell B v) ↔ cellLex k (cell B u) (cell B v) :=
  order_lt k (pitch rank) (cell B u) (cell B v) (cell_room B u).1 (cell_room B v).1

theorem header_before_lex (e f : (coarse).graph.Edge) :
    let x:=header e
    let y:=header f
    decide (cellLex k x.src y.src ∨ (x.src=y.src ∧ x.ordinal<y.ordinal))=
      decide (earlier B e f) := by
  intro x y
  rw [←header_before B e f]
  change decide (cellLex k x.src y.src ∨ _) = decide (siteOrder B x.src<siteOrder B y.src ∨ _)
  have lexs := siteOrder_lt B ((coarse).graph.src e) ((coarse).graph.src f)
  change (siteOrder B x.src<siteOrder B y.src ↔ cellLex k x.src y.src) at lexs
  apply decide_eq_decide.mpr
  exact or_congr lexs.symm Iff.rfl

theorem observed_before (e f : (coarse).graph.Edge) (atE atF : ℕ) (rowE rowF : Fin 7→ℕ)
    (idE : atE=((Z).installedResetOrdinal T vertex birth e).val)
    (idF : atF=((Z).installedResetOrdinal T vertex birth f).val)
    (readE : rowE=(Z).actualRecord T vertex e) (readF : rowF=(Z).actualRecord T vertex f) :
    let x:=recordTag atE rowE
    let y:=recordTag atF rowF
    decide (cellLex k x.src y.src ∨ (x.src=y.src ∧ x.ordinal<y.ordinal))=
      decide (earlier B e f) := by
  dsimp only
  rw [readE,readF,idE,idF,recordTag_read B e,recordTag_read B f]
  exact header_before_lex B e f

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
