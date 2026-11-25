import OAI.ThreeFlat.Diagonal.NavigationPass
import OAI.ThreeFlat.Diagonal.PhysicalRefreshContract
import OAI.ThreeFlat.Diagonal.RefreshCursorFrame

namespace OAI
/-! # Admission of untrusted refresh count words under the computed tile descriptor -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory
open CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Read a physical three-column descriptor together with the preserved dense rows. -/
private theorem bank_layout {W K n : ℕ} (family : RecordFamily n) (fit : family.Fits K W)
    (x : HistogramRegister.Words family.motifs K W) (mem : Memory W)
    (ctrl dense desc : ℕ) (key : Fin family.motifs → ℕ)
    (count : AdmissionBank.rowCount ctrl mem=family.motifs)
    (base : AdmissionBank.denseBase ctrl mem=dense) (header : AdmissionBank.descBase ctrl mem=desc)
    (kFit : K<2^W)
    (data : ∀ (i : Fin family.motifs) (j : Fin K),mem (dense+i.val*K+j.val)=x i j)
    (table : ∀ (i : Fin family.motifs) (f : Fin 3),mem (desc+(i.val*3+f.val))=
      ((if f.val=0 then family.copies i else if f.val=1 then key i else Fintype.card (family.alphabet i) : ℕ) : Word W)) :
    HistogramRegister.BankLayout ctrl (family.rows fit) x mem := by
  refine ⟨count,?_,?_,?_⟩
  · intro i
    have word : mem (desc+(i.val*3+2))=((Fintype.card (family.alphabet i) : ℕ) : Word W) :=
      table i ⟨2,by decide⟩
    have fits := (fit.1 i).trans_lt kFit
    change (mem (AdmissionBank.descBase ctrl mem+3*i.val+2)).val=_
    simp only [header,Nat.mul_comm 3,Nat.add_assoc,word,Fin.val_cast_of_lt fits,RecordFamily.rows]
  · intro i
    have word : mem (desc+(i.val*3+0))=((family.copies i : ℕ) : Word W) := table i ⟨0,by decide⟩
    change (mem (AdmissionBank.descBase ctrl mem+3*i.val)).val=_
    simpa only [RecordFamily.rows,header,Nat.mul_comm 3,Nat.add_zero,Fin.val_cast_of_lt (fit.2 i)] using congrArg Fin.val word
  · intro i j
    rw [base,Nat.mul_comm K]
    exact data i j

variable {F : Type} [Field F] {W s rem h pad K : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)
set_option quotPrecheck false
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "v" => Fintype.card A.Base
local notation "m" => 2^s

theorem refresh_bank (cur : Word W) (input : Memory W) (csr : Cursor)
    (u : CursorSpace cur input csr K v s rem h pad)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) (oldColumns csr v m) (fun i=>(input i).val) A.width)
    (fit : (Q).Fits K W) (x : HistogramRegister.Words (Q).motifs K W)
    (raw : ∀ (i : Fin (Q).motifs) (j : Fin K),input (csr.dense+i.val*K+j.val)=x i j)
    (ports : m<2^W) (lanes : 2^rem<2^W) (tiles : T.last+1≤2^W) (Kfit : K<2^W)
    (room : 1+2*m*m*A.maxWidth+refreshBaseBound T<2^W) :
    let pre := preparation cur T.base (fun j=>Fintype.card (T.block j).Alphabet)
    let mid := pre.run input
    AdmissionBank.Fits cur.val K mid ∧ HistogramRegister.BankLayout cur.val ((Q).rows fit) x mid := by
  let entries := allocate K csr (.refresh v m (2^rem) h pad)
  let size := fun j=>Fintype.card (T.block j).Alphabet
  let code := preScans cur T.base size
  let mid := (preparation cur T.base size).run input
  change AdmissionBank.Fits cur.val K mid ∧ HistogramRegister.BankLayout cur.val ((Q).rows fit) x mid
  let before := fun i : ℕ => i<csr.heap ∨ entries.next.heap≤ i
  have pass := code.run_spec cur input csr.header 63 entries.words before u.header (.inr u.controls) u.start_live (u.pre_safe _ _)
  have kept : ∀ i,before i → mid i=input i := pass.2.2
  have um : CursorSpace cur mid csr K v s rem h pad := u.frame _ kept
  have hw := refresh_prepare_physical T A hm hh sym rows zero conn cur input (oldColumns csr v m) (entries.words 12)
    csr.heap old u.prepare ports lanes tiles room
  have count : AdmissionBank.rowCount cur.val mid=(Q).motifs := by
    exact um.read 0 (by decide)
  have dense : AdmissionBank.denseBase cur.val mid=csr.dense := um.read 1 (by decide)
  have choice : AdmissionBank.descBase cur.val mid=csr.heap := um.read 2 (by decide)
  have words (i : Fin (Q).motifs) (j : Fin K) : mid (csr.dense+i.val*K+j.val)=x i j := by
    apply Eq.trans (kept _ ?_) (raw i j)
    left
    have key : i.val*K+j.val < (Q).motifs*K := (Nat.add_lt_add_left j.isLt _).trans_le (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right K i.isLt)
    have top : csr.dense+(Q).motifs*K≤csr.heap := u.counts
    omega
  have live := um.prepare
  constructor
  · refine ⟨cur.isLt,?_,?_,?_⟩
    · have current : (mid cur.val).val+19<2^W := live.header
      omega
    · rw [dense,count,Nat.mul_comm K]
      have oldEnd : csr.dense+(Q).motifs*K≤csr.heap := u.counts
      have stop : csr.heap+3*(Q).motifs<2^W := live.choiceCap
      omega
    · rw [choice,count]
      exact live.choiceCap.le
  · exact bank_layout (Q) fit x mid cur.val csr.dense csr.heap _ count dense choice Kfit words hw.2

theorem refresh_read_table (fit : (Q).Fits K W) (x : HistogramRegister.Words (Q).motifs K W)
    (b : Fin (refreshBinary T A hm hh sym rows zero conn).rules.count)
    (chosen : ((Q).record fit).read (List.ofFn (HistogramRegister.bitTable x))=some b) :
    HistogramRegister.words ((Q).rows fit) ((Q).sequence fit b)=x := by
  have bits := ((Q).record fit).write_read _ _ chosen
  have eq := List.ofFn_inj.mp bits
  exact HistogramRegister.bitTable.injective eq


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
