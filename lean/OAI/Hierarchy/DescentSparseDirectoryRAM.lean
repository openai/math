import OAI.Hierarchy.DescentSparseApertureRAM

namespace OAI
/-! # Whole fixed-aperture native publication for an occupied source colony -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM.Rect
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentFirstColonyRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {H p R w : ℕ}

def slots (p R : ℕ) := (p+1)*R+1

structure Storage where
  raw : Bank
  cleaned : Bank
  scratch : ℕ
  sorted : ℕ

structure Fits (s : Storage) (M w : ℕ) : Prop where
  rawRange : M≤ s.raw.size
  rawEnd : s.raw.Fits w s.cleaned.base
  cleanRange : M≤ s.cleaned.size
  cleanEnd : s.cleaned.Fits w s.scratch
  disjoint : s.scratch+M+M≤ s.sorted
  result : s.sorted+M<2^w

def prep (s : Storage) (n missing : ℕ) (e : Expr) (m : Memory w) :=
  ProtocolRAM.image s.cleaned.base n (clean n missing s.raw) (ProtocolRAM.image s.raw.base n e m)

def observed (s : Storage) (n : ℕ) (m : Memory w) (i : Fin n) := (m (s.cleaned.base+i.val)).val

def machine (w n missing : ℕ) (s : Storage) (e : Expr) :=
  ((scan w s.raw.base n e).seq (scan w s.cleaned.base n (clean n missing s.raw))).seq
    (SparseBinRAM.program w n s.scratch s.sorted s.cleaned (.lookup s.cleaned .row))

def out (n missing : ℕ) (s : Storage) (e : Expr) (m : Memory w) :=
  let b := prep s n missing e m
  after s.scratch s.sorted s.cleaned (.lookup s.cleaned .row) (observed s n b) b

def clocks (n missing : ℕ) (s : Storage) (e : Expr) :=
  (4+n*(2*e.work+4))+(4+n*(2*(clean n missing s.raw).work+4))+
    ticks n s.sorted s.cleaned (.lookup s.cleaned .row)

theorem exec (n missing : ℕ) (s : Storage) (e : Expr) (m : Memory w) (space : Fits s n w)
    (read : e.Fits w s.raw.base) :
    (machine w n missing s e).Exec m (out n missing s e m) (clocks n missing s e) := by
  have a := space.rawEnd.2.2
  have b := space.cleanEnd.2.2
  have c := space.disjoint
  have d := space.result
  have x := space.rawRange
  have y := space.cleanRange
  let memoryRaw := ProtocolRAM.image s.raw.base n e m
  let cleanPass := clean n missing s.raw
  let value : Expr := .lookup s.cleaned .row
  have rawFit : s.raw.base + n < 2^w := by omega
  have cleanFit : s.cleaned.base + n < 2^w := by omega
  have rawStep := @scan_exec w s.raw.base n e m read rawFit
  have cleanStep := @scan_exec w s.cleaned.base n cleanPass memoryRaw
    (clean_fits n missing s.cleaned.base s.raw space.rawEnd) cleanFit
  have vf : value.Fits w s.scratch := ⟨space.cleanEnd,trivial⟩
  have finalStep := @SparseBinRAM.run n w s.scratch s.sorted s.cleaned value
    (observed s n (prep s n missing e m)) (prep s n missing e m) space.cleanRange space.cleanEnd
    vf space.disjoint space.result (fun _ => rfl)
  exact @Procedure.Exec.then w
    ((scan w s.raw.base n e).seq (scan w s.cleaned.base n cleanPass))
    (SparseBinRAM.program w n s.scratch s.sorted s.cleaned value)
    m (prep s n missing e m) (out n missing s e m) _ _
    (@Procedure.Exec.then w (scan w s.raw.base n e) (scan w s.cleaned.base n cleanPass)
      m memoryRaw (prep s n missing e m) _ _ (@rawStep) (@cleanStep))
    (@finalStep)

theorem clocks_le (n missing : ℕ) (s : Storage) (e : Expr) :
    clocks n missing s e≤19+n*(130*n+2*e.work+80) := by
  have t := ticks_le n s.sorted s.cleaned (.lookup s.cleaned .row)
  simp only [clocks,clean_work,Expr.work] at *
  nlinarith only [t]

theorem old (n missing : ℕ) (s : Storage) (e : Expr) (m : Memory w) (space : Fits s n w)
    {x : ℕ} (early : x<s.raw.base) : out n missing s e m x=m x := by
  have a := space.rawEnd.2.2
  have b := space.cleanEnd.2.2
  have c := space.disjoint
  exact (SparseBinRAM.below s.scratch s.sorted s.cleaned (.lookup s.cleaned .row)
    (observed s n (prep s n missing e m)) (prep s n missing e m) (x:=x)
    (show x < s.scratch by omega) (show s.scratch ≤ s.sorted by omega)).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl early)))

theorem sorted_source_missing [Nonempty C] (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H))
    (s : Storage) (L : Chart) (src : Fin (p+1)→Expr) (m : Memory w)
    (space : Fits s (slots p R) w) (headers : Headers L (cell.trans finProdFinEquiv.toEmbedding) m)
    (seen : ∀(i : Fin (slots p R)) q,(src q).eval m (i.val:Word w)=(portWord ports q:Word w))
    (host : H<2^w) (size : H*R≤L.heads.size) (headFit : L.heads.size<2^w)
    (i : Fin (slots p R)) :
    let A := installed cell ports
    let e := expr H p R (H*R) L src
    out (slots p R) (H*R) s e m (s.sorted+(order A.key i).val)=((wideTag (H*R) (A.target i)):Word w) := by
  let n := slots p R
  let missing := H*R
  have smallCard : Fintype.card C≤ missing := cell_card cell
  have card : missing<2^w := size.trans_lt headFit
  let e := expr H p R missing L src
  let A := installed cell ports
  let raw := rawName cell ports
  let a := ProtocolRAM.image s.raw.base n e m
  let b := prep s n missing e m
  have nf : n<2^w := space.rawRange.trans_lt space.rawEnd.2.1
  have tagFit (q : Option C) : wideTag missing q<2^w := by
    cases q with
    | none => exact card
    | some v => exact (code_lt v).trans (smallCard.trans_lt card)
  have inputs (j : Fin n) : (a (s.raw.base+j.val)).val=wideTag missing (raw j) := by
    have tap := (ProtocolRAMGeneratedWrite.read_image s.raw.base n e m j).trans
      (eval_missing missing cell ports L src m j headers (seen j) host nf.le size headFit)
    exact (congrArg Fin.val tap).trans (Fin.val_cast_of_lt (tagFit _))
  have data (j : Fin n) : b (s.cleaned.base+j.val)=((wideTag missing (A.target j)):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image s.cleaned.base n (clean n missing s.raw) a j).trans
      (clean_eval_missing raw s.raw a j space.rawRange space.rawEnd.2.1 missing smallCard card inputs)
  have same : observed s n b=fun i=>wideTag missing (A.target i) := by
    funext j
    exact (congrArg Fin.val (data j)).trans (Fin.val_cast_of_lt (tagFit (A.target j)))
  change after s.scratch s.sorted s.cleaned (.lookup s.cleaned .row) (observed s n b) b _=_
  rw [same]
  have ranks : order (fun j : Fin n => wideTag missing (A.target j)) = order A.key :=
    upper_order A.target missing smallCard
  have place := congrArg (fun ord : Equiv.Perm (Fin n) => s.sorted + (ord i).val) ranks
  erw [← place]
  apply (publish s.scratch s.sorted s.cleaned (.lookup s.cleaned .row) (fun i=>wideTag missing (A.target i)) b i).trans
  have small := i.isLt.trans_le space.cleanRange
  simpa [Expr.eval,Bank.read,Fin.val_cast_of_lt (small.trans space.cleanEnd.2.1),Nat.mod_eq_of_lt small] using data i

theorem sorted_source (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H))
    (s : Storage) (L : Chart) (src : Fin (p+1)→Expr) (m : Memory w)
    (space : Fits s (slots p R) w) (headers : Headers L (cell.trans finProdFinEquiv.toEmbedding) m)
    (seen : ∀(i : Fin (slots p R)) q,(src q).eval m (i.val:Word w)=(portWord ports q:Word w))
    (host : H<2^w) (card : Fintype.card C<2^w) (size : H*R≤L.heads.size) (headFit : L.heads.size<2^w)
    (i : Fin (slots p R)) :
    let A := installed cell ports
    let e := expr H p R (Fintype.card C) L src
    out (slots p R) (Fintype.card C) s e m (s.sorted+(order A.key i).val)=(A.key i:Word w) := by
  let n := slots p R
  let missing := Fintype.card C
  let e := expr H p R missing L src
  let A := installed cell ports
  let raw := rawName cell ports
  let a := ProtocolRAM.image s.raw.base n e m
  let b := prep s n missing e m
  have nf : n<2^w := space.rawRange.trans_lt space.rawEnd.2.1
  have tagFit (q : Option C) : tag q<2^w := by
    cases q with
    | none => exact card
    | some v => exact (code_lt v).trans card
  have inputs (j : Fin n) : (a (s.raw.base+j.val)).val=tag (raw j) := by
    have tap := (ProtocolRAMGeneratedWrite.read_image s.raw.base n e m j).trans
      (eval cell ports L src m j headers (seen j) host nf.le size headFit)
    exact (congrArg Fin.val tap).trans (Fin.val_cast_of_lt (tagFit _))
  have data (j : Fin n) : b (s.cleaned.base+j.val)=(A.key j:Word w) :=
    (ProtocolRAMGeneratedWrite.read_image s.cleaned.base n (clean n missing s.raw) a j).trans
      (clean_eval raw s.raw a j space.rawRange space.rawEnd.2.1 card inputs)
  have same : observed s n b=A.key := by
    funext j
    exact (congrArg Fin.val (data j)).trans (Fin.val_cast_of_lt (tagFit (A.target j)))
  change after s.scratch s.sorted s.cleaned (.lookup s.cleaned .row) (observed s n b) b _=_
  rw [same]
  apply (publish s.scratch s.sorted s.cleaned (.lookup s.cleaned .row) A.key b i).trans
  have small := i.isLt.trans_le space.cleanRange
  simpa [Expr.eval,Bank.read,Fin.val_cast_of_lt (small.trans space.cleanEnd.2.1),Nat.mod_eq_of_lt small] using data i

end Hierarchy.DescentPacking.SparseBinRAM.Rect

end
end OAI
