import OAI.ThreeFlat.RAM.PhysicalPinsNat
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Native pin-map lookup at an occupied local party

Supply rows consist of a per-bit pointer-array address and payload width.
Demand rows consist of a per-bit pointer-array address, physical width and tile digit
width. A fixed finite tile LUT maps each local header bit (after its
selector) to a demand port and the within-port digit. Address zero in a
demand row denotes an identically false old port. Only selected local
parties materialize these arrays. A balanced demand can use several old
child streams in one word.
-/
namespace ThreeFlat.RAM.HistoryPartyGather

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

structure Layout where
  copies : ℕ
  selectorBits : ℕ
  ports : ℕ
  headerBits : ℕ
  tileBits : ℕ
  anchor : ℕ
  supplyRows : ℕ
  demandRows : ℕ
  headerTable : ℕ

def Layout.args (L : Layout) (pin : ℕ) : Fin 10 → ℕ :=
  ![pin,L.copies,L.selectorBits,L.ports,L.headerBits,L.tileBits,L.anchor,L.supplyRows,L.demandRows,L.headerTable]

private abbrev E := Formula 10
private abbrev v (i : Fin 10) : E := .reg i
private def field (base step i j : E) := (.load (add (add base (mul step i)) j) : E)
private def supplied (port pos : E) := (.load (add (field (v 7) (L 2) port (L 0)) pos) : E)
private def payload (port : E) := field (v 7) (L 2) port (L 1)
private def selectBit (port copy j : E) := supplied port (add (payload port) (add (mul (v 2) copy) j))
private def previous (copy x : E) : E :=
  let port := field (v 9) (L 2) x (L 0)
  let digit := field (v 9) (L 2) x (L 1)
  let q (j : ℕ) := field (v 8) (L 3) port (L j)
  let atBit := add (mul (q 2) copy) digit
  eqz (q 0) (L 0) (L 0) (lt atBit (q 1) (.load (add (q 0) atBit)) (L 0))

def formula : E :=
  let x := v 0; let r := v 1; let k := v 2; let e := v 3; let h := v 4; let d := v 5
  let selectors := mul r (mul e k); let rest := sub x selectors
  let copy := div rest h; let localBit := rem rest h
  let tail := sub rest (mul r h); let stride := mul r d
  let port := div tail stride; let pos := rem tail stride
  lt x selectors (selectBit (rem (div x k) e) (div x (mul e k)) (rem x k))
    (lt rest (mul r h) (lt localBit k (selectBit (v 6) copy localBit) (previous copy (sub localBit k)))
      (lt pos (payload port) (supplied port pos) (L 0)))

def gather (T : Layout) (mem : ℕ → ℕ) (x : ℕ) : ℕ :=
  let supply (a j : ℕ) := mem (T.supplyRows+2*a+j)
  let selector (a i t : ℕ) := mem (supply a 0 + (supply a 1+(T.selectorBits*i+t)))
  let sel := T.copies*(T.ports*T.selectorBits)
  if x<sel then selector ((x/T.selectorBits)%T.ports) (x/(T.ports*T.selectorBits)) (x%T.selectorBits) else
    let y := x-sel
    if y<T.copies*T.headerBits then
      let copy := y/T.headerBits; let atBit := y%T.headerBits
      if atBit<T.selectorBits then selector T.anchor copy atBit else
        let index := T.headerTable+2*(atBit-T.selectorBits); let port := mem index
        let row := T.demandRows+3*port; let bit := mem (row+2)*copy+mem (index+1)
        if mem row=0 then 0 else if bit<mem (row+1) then mem (mem row+bit) else 0
    else let z := y-T.copies*T.headerBits; let stride := T.copies*T.tileBits
         let a := z/stride; let i := z%stride
         if i<supply a 1 then mem (supply a 0+i) else 0

theorem natural (W : ℕ) (pub : Param → ℕ) (mem : ℕ → ℕ) (T : Layout) (x : ℕ) :
    formula.natural W pub mem (T.args x)=gather T mem x := by
  let sel := T.copies*(T.ports*T.selectorBits)
  let y := x-sel
  let body := T.copies*T.headerBits
  let t := y % T.headerBits
  let hdr := T.headerTable+2*(t-T.selectorBits)
  let row := T.demandRows+3*mem hdr
  let bit := mem (row+2)*(y/T.headerBits)+mem (hdr+1)
  let pos := (y-body)%(T.copies*T.tileBits)
  let port := (y-body)/(T.copies*T.tileBits)
  by_cases f : x < sel
  · dsimp only [sel] at f
    simp [formula,gather,Layout.args,field,supplied,payload,selectBit,previous,Formula.natural,natOp,natTest,f]
  · by_cases g : y < body
    · by_cases s : t < T.selectorBits
      · dsimp only [sel,y,body,t] at f g s
        simp [formula,gather,Layout.args,field,supplied,payload,selectBit,previous,Formula.natural,natOp,natTest,f,g,s]
      · by_cases z : mem row = 0 <;> by_cases demand : bit < mem (row+1) <;>
          dsimp only [sel,y,body,t,hdr,row,bit] at f g s z demand <;>
          simp [formula,gather,Layout.args,field,supplied,payload,selectBit,previous,Formula.natural,natOp,natTest,f,g,s,z,demand]
    · by_cases inside : pos < mem (T.supplyRows+2*port+1) <;>
        dsimp only [sel,y,body,t,pos,port] at f g inside <;>
        simp [formula,gather,Layout.args,field,supplied,payload,selectBit,previous,Formula.natural,natOp,natTest,f,g,inside]

def program (W : ℕ) : Term W 1 10 := formula.compile (fun _ => 0)

set_option maxRecDepth 4096 in
theorem binds (W : ℕ) : (program W).binds ≤ 1000 := by rw [program,Formula.binds_compile]; decide

theorem eval (W : ℕ) (pub : Fin 1 → ℕ) (mem : ℕ → ℕ) (T : Layout) (x : ℕ)
    (fit : formula.Fits W (fun _ => pub 0) mem (T.args x)) :
    (program W).eval (fun i => (pub i : Word W)) (fun a => (mem a : Word W)) (fun j => (T.args x j : Word W)) =
      (gather T mem x : Word W) := by
  rw [program,Formula.eval_compile]
  exact (Formula.value_eq_natural formula (fun _ => pub 0) mem _ fit).trans
    (congrArg (fun v : ℕ => (v : Word W)) (natural W _ mem T x))

/-- Addresses used by a single gathered pin. For a demand digit the metadata
row is indexed by the selected header-table entry. Its payload is read only
when the digit lies within the physical word. -/
def AddressesFit (W : ℕ) (T : Layout) (m : ℕ→ℕ) (x : ℕ) : Prop :=
  let limit := 2^W
  let selectors := T.copies*(T.ports*T.selectorBits)
  let remaining := x-selectors
  let fromSupply (p off : ℕ) := T.supplyRows+2*p+1<limit ∧ m (T.supplyRows+2*p)+off<limit
  let atSelector (p i j : ℕ) := fromSupply p (m (T.supplyRows+2*p+1)+(T.selectorBits*i+j))
  if x<selectors then atSelector ((x/T.selectorBits)%T.ports) (x/(T.ports*T.selectorBits)) (x%T.selectorBits)
  else if remaining<T.copies*T.headerBits then
    let i := remaining/T.headerBits
    let t := remaining%T.headerBits
    if t<T.selectorBits then atSelector T.anchor i t else
      let hdr := T.headerTable+2*(t-T.selectorBits)
      let row := T.demandRows+3*m hdr
      let bit := m (row+2)*i+m (hdr+1)
      hdr+1<limit ∧ row+2<limit ∧ bit<limit ∧ (m row≠0 → bit<m (row+1) → m row+bit<limit)
  else let tail := remaining-T.copies*T.headerBits
       let stride := T.copies*T.tileBits
       let p := tail/stride
       let t := tail%stride
       T.supplyRows+2*p+1<limit ∧ (t<m (T.supplyRows+2*p+1) → m (T.supplyRows+2*p)+t<limit)

set_option maxHeartbeats 1000000 in
/-- Fit of the real heterogeneous gather formula follows from its scalar
widths and the extents of the table pages and selected port apertures. -/
theorem fits_of_addresses (W : ℕ) (pub : Param→ℕ) (T : Layout) (m : ℕ→ℕ) (x : ℕ)
    (scalars : 2+x+T.selectorBits+T.ports+T.headerBits+T.ports*T.selectorBits+
      T.copies*(T.ports*T.selectorBits)+T.copies*T.headerBits+T.copies*T.tileBits<2^W)
    (words : ∀ i,m i<2^W) (addr : AddressesFit W T m x) : formula.Fits W pub m (T.args x) := by
  have xr : x<2^W := by omega
  have cut (a b : ℕ) (ha : a<2^W) : a-b<2^W := (Nat.sub_le a b).trans_lt ha
  have divFit (a b : ℕ) (ha : a<2^W) : a/b<2^W := (Nat.div_le_self a b).trans_lt ha
  have modFit (a b : ℕ) (ha : a<2^W) : a%b<2^W := (Nat.mod_le _ _).trans_lt ha
  let sel := T.copies*(T.ports*T.selectorBits)
  let rest := x-sel
  let body := T.copies*T.headerBits
  let t := rest%T.headerBits
  let hdr := T.headerTable+2*(t-T.selectorBits)
  let row := T.demandRows+3*m hdr
  let digit := m (row+2)*(rest/T.headerBits)+m (hdr+1)
  let tail := rest-body
  let stride := T.copies*T.tileBits
  let u := tail/stride
  let b := tail%stride
  have handled : ∀ a, m a<2^W := words
  have scal : T.selectorBits<2^W ∧ T.ports<2^W ∧ T.headerBits<2^W ∧ T.ports*T.selectorBits<2^W ∧
      sel<2^W ∧ body<2^W ∧ stride<2^W ∧ 0<2^W := by dsimp [sel,body,stride];omega
  rcases scal with ⟨kB,eB,hB,ekB,sB,bB,rB,zero⟩
  by_cases first : x<sel
  · change (if x<sel then _ else _) at addr
    rw [ite_eq_left first] at addr
    obtain ⟨one,last⟩ := addr
    have page : T.supplyRows+2*(x/T.selectorBits%T.ports)<2^W := by omega
    simp (disch := first | assumption | apply handled | solve_by_elim [cut,divFit,modFit] | omega)
      [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
        natOp,natTest,opFits,show T.copies*(T.ports*T.selectorBits)=sel from rfl,first,page,one,last]
    all_goals repeat' apply And.intro
    all_goals first | assumption | solve_by_elim [cut,divFit,modFit]
  · by_cases second : rest<body
    · by_cases third : t<T.selectorBits
      · change (if x<sel then _ else if rest<body then (if t<T.selectorBits then _ else _) else _) at addr
        rw [ite_eq_right first,ite_eq_left second,ite_eq_left third] at addr
        obtain ⟨one,last⟩ := addr
        have page : T.supplyRows+2*T.anchor<2^W := by omega
        dsimp only [sel,rest,body,t] at first second third one last sB bB
        simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
          natOp,natTest,opFits,first,second,third,one,last,sB,bB]
        all_goals repeat' apply And.intro
        all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]
      · change (if x<sel then _ else if rest<body then (if t<T.selectorBits then _ else _) else _) at addr
        rw [ite_eq_right first,ite_eq_left second,ite_eq_right third] at addr
        rcases addr with ⟨endHeader,endRow,digitFit,read⟩
        change hdr+1 < 2^W at endHeader
        change row+2 < 2^W at endRow
        change digit < 2^W at digitFit
        change m row ≠ 0 → digit < m (row+1) → m row+digit < 2^W at read
        have h0 : hdr<2^W := by omega
        have d0 : row<2^W := by omega
        have d1 : row+1<2^W := by omega
        by_cases present : m row=0
        · dsimp only [sel,rest,body,t,hdr,row,digit] at first second third endHeader endRow h0 d0 d1 digitFit present sB bB
          simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
            natOp,natTest,opFits,first,second,third,h0,d0,present,sB,bB]
          all_goals repeat' apply And.intro
          all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]
        · by_cases inside : digit<m (row+1)
          · have live := read present inside
            dsimp only [sel,rest,body,t,hdr,row,digit] at first second third endHeader endRow h0 d0 d1 digitFit present inside live sB bB
            simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
              natOp,natTest,opFits,first,second,third,endHeader,endRow,h0,d0,d1,digitFit,present,inside,live,sB,bB]
            all_goals repeat' apply And.intro
            all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]
          · dsimp only [sel,rest,body,t,hdr,row,digit] at first second third endHeader endRow h0 d0 d1 digitFit present inside sB bB
            simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
              natOp,natTest,opFits,first,second,third,endHeader,endRow,h0,d0,d1,digitFit,present,inside,sB,bB]
            all_goals repeat' apply And.intro
            all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]
    · change (if x<sel then _ else if rest<body then _ else _) at addr
      rw [ite_eq_right first,ite_eq_right second] at addr
      obtain ⟨one,read⟩ := addr
      change T.supplyRows+2*u+1 < 2^W at one
      change b < m (T.supplyRows+2*u+1) → m (T.supplyRows+2*u)+b < 2^W at read
      have page : T.supplyRows+2*u<2^W := by omega
      by_cases inside : b<m (T.supplyRows+2*u+1)
      · have live := read inside
        dsimp only [sel,rest,body,tail,stride,u,b] at first second one page inside live sB bB rB
        simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
          natOp,natTest,opFits,first,second,one,page,inside,live,sB,bB,rB]
        all_goals repeat' apply And.intro
        all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]
      · dsimp only [sel,rest,body,tail,stride,u,b] at first second one page inside sB bB rB
        simp [formula,Layout.args,selectBit,supplied,payload,field,previous,Formula.Fits,Formula.natural,
          natOp,natTest,opFits,first,second,one,inside,sB,bB,rB]
        all_goals repeat' apply And.intro
        all_goals first | assumption | apply handled | solve_by_elim [cut,divFit,modFit]

end ThreeFlat.RAM.HistoryPartyGather

end OAI
