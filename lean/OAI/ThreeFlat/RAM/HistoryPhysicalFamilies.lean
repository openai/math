import OAI.ThreeFlat.RAM.HistoryPhysicalLibrary
import OAI.ThreeFlat.RAM.HistoryStageBody
import OAI.ThreeFlat.RAM.HistoryPartySpecialization
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.ShrinkSiteTree
import OAI.ThreeFlat.Diagonal.RefreshSiteTree
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal

namespace OAI
/-! # Immutable party tables of the finite physical shrink and refresh program -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.MotifSelector
open CompressorPacking MotifOuterTerms HistogramTileNetwork Expander
open scoped Classical BigOperators Fin.CommRing

noncomputable section

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem increasing_ports (B : PhysicalStage.Block F) : StrictMono (fun i : ℕ => (2:ℕ)^B.exponent i) := by
  apply strictMono_nat_of_lt_succ
  intro i
  let d := (2:ℕ)^B.exponent i
  let D := (2:ℕ)^B.exponent (i+1)
  let g := (2:ℕ)^(2*d+1)*d*d
  have hd : 0<d := by dsimp [d];positivity
  have hD : (0:ℝ)<D := by dsimp [D];positivity
  have hg : d≤g := by
    have ht : 0<(2:ℕ)^(2*d+1)*d := by positivity
    exact Nat.le_mul_of_pos_left d ht
  have hh : (g:ℝ)/D≤1/1024 := by simpa only [g,d,D,Nat.cast_pow,Nat.cast_ofNat] using B.small i
  have raw := (div_le_iff₀ hD).mp hh
  have dpos : (0:ℝ)<d := by exact_mod_cast hd
  have gmin : (d:ℝ)≤g := by exact_mod_cast hg
  have : (d:ℝ)<D := by linarith
  exact_mod_cast this

omit [Fintype F] in
theorem shrink_ports_injective (B : PhysicalStage.Block F) :
    Function.Injective (fun i : Fin B.levels => (shrinkGrid B i).oldPorts) := by
  intro i j hi
  apply Fin.ext
  exact (increasing_ports B).injective hi

def Grid.family (G : Grid F) (start : ℕ) : Family :=
  ⟨G.mode,G.oldPorts,G.childBound,G.motifs,G.parties,G.demand,G.supply,G.digits,start,
    start+7*G.rows.length⟩

def familiesFrom : ℕ → List (Grid F) → List Family
  | _,[] => []
  | start,g::gs => g.family start :: familiesFrom (start+g.size) gs

def archive (B : PhysicalStage.Block F) (start height histStride : ℕ) : Archive :=
  ⟨start+StableCompactROMNative.size height,HistoryStaticArchive.stride (arity B),
    start,StableCompactROMPool.page height 12,start+StableCompactROMNative.size height+staticSize B,histStride⟩

def families (B : PhysicalStage.Block F) (start height : ℕ) :=
  familiesFrom (start+StableCompactROMNative.size height+staticSize B+HistoryCompactorCounts.size height) (grids B)

private theorem sum_mem (l : List ℕ) (x : ℕ) (hx : x∈l) : x≤l.sum := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl|ht
    · simp
    · have := ih ht; simp only [List.sum_cons];omega

omit [Field F] [Fintype F] in
theorem Grid.caps (G : Grid F) {p : Party F} (mem : p∈G.rows) :
    p.demands≤G.demand ∧ p.supplies≤G.supply ∧ p.port.digits≤G.digits :=
  ⟨sum_mem _ _ (List.mem_map.mpr ⟨p,mem,rfl⟩),sum_mem _ _ (List.mem_map.mpr ⟨p,mem,rfl⟩),
   sum_mem _ _ (List.mem_map.mpr ⟨p,mem,rfl⟩)⟩

omit [Fintype F] in
theorem arity_fits (B : PhysicalStage.Block F) {G : Grid F} (g : G∈grids B) {p : Party F} (cell : p∈G.rows) :
    p.header+(p.supplies*p.maxDigit+p.supplies*p.maxDigit)≤arity B ∧ p.supplies*p.codeBits+p.letters≤arity B := by
  have bound : p.bound≤arity B := sum_mem _ _ (List.mem_flatMap.mpr ⟨G,g,List.mem_map.mpr ⟨p,cell,rfl⟩⟩)
  unfold Party.bound at bound
  omega

private theorem slab_read {α β : Type*} {k : ℕ} (f : α→Fin k→β)
    (xs : List α) (i : Fin xs.length) (j : Fin k) :
    (xs.flatMap fun x=>List.ofFn (f x))[k*i.val+j.val]?=some (f (xs.get i) j) := by
  induction xs with
  | nil => exact i.elim0
  | cons x xs ih =>
    refine Fin.cases ?_ (fun u=>?_) i
    · simp [List.flatMap_cons,List.getElem?_append_left (by simp : j.val<(List.ofFn (f x)).length),j.isLt]
    · have pos : k*u.succ.val+j.val=(List.ofFn (f x)).length+(k*u.val+j.val) := by simp [Nat.mul_succ];omega
      have selected : (x::xs).get u.succ=xs.get u := by
        cases u
        rfl
      simpa only [List.flatMap_cons,pos,List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left,selected] using ih u

omit [Field F] [Fintype F] in
theorem grid_row {n p : ℕ} (f : Fin n→Fin p→Party F) (i : Fin n) (j : Fin p) :
    (grid f)[p*i.val+j.val]?=some (f i j) := by
  let x : Fin (List.finRange n).length := ⟨i.val,by simp⟩
  have fetched := slab_read f (List.finRange n) x j
  simpa [grid,x,List.get_eq_getElem] using fetched

omit [Field F] [Fintype F] in
theorem grid_has {n p : ℕ} (f : Fin n→Fin p→Party F) (i : Fin n) (j : Fin p) : f i j∈grid f :=
  List.mem_of_getElem? (grid_row f i j)

omit [Field F] in
private theorem kind_at_bounds (p : Party F) (ar : ℕ)
    (tileFits : p.header+(p.supplies*p.maxDigit+p.supplies*p.maxDigit)≤ar)
    (admitFits : p.supplies*p.codeBits+p.letters≤ar) :
    p.kind ar=⟨p.supplies,p.letters,p.codeBits,p.header,p.maxDigit,
      (HistoryStaticArchive.index F ar tileFits p.tile).val,
      (HistoryStaticArchive.index F ar admitFits p.admit).val⟩ := by
  simp only [Party.kind,dite_eq_left tileFits,dite_eq_left admitFits]

theorem Party.kind_ofTile {J E S : Type} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
    (D : PortGraph J E) (G : Supply J S) (j : J) (base : E→ℕ)
    (T : FixedMotifTile D (ports G) base F) {n e ar : ℕ} (dp : Fin n ≃ D.Port j)
    (sp : Fin e ≃ (ports G).Port j) (di : Fin n→ℕ) (si : Fin e→ℕ)
    (bounds : let p := Party.ofTile D G j base T dp sp di si
      p.header+(p.supplies*p.maxDigit+p.supplies*p.maxDigit)≤ar ∧ p.supplies*p.codeBits+p.letters≤ar) :
    letI := T.hasLetter
    let B : Header (D.Port j) T.Alphabet (fun q=>base q.1.1) T.bits n := ⟨dp,T.encode⟩
    let tile := HistogramTileNetwork.tile D G j base B sp T.output (fun z a=>T.output_le_cap z (sp a).1.1) T.entry
    let good := headerGood G j sp T.encode
    let letter := headerLetter G j sp (Fintype.equivFin _) T.encode
    (Party.ofTile D G j base T dp sp di si).kind ar=HistoryPartySpecialization.kind tile good letter bounds.1 bounds.2 := by
  exact kind_at_bounds (Party.ofTile D G j base T dp sp di si) ar bounds.1 bounds.2


omit [Field F] in
theorem Grid.kind_word (G : Grid F) (ar : ℕ) (i : Fin G.rows.length) (j : Fin 7) :
    (G.words ar)[7*i.val+j.val]?=some (((G.rows.get i).kind ar).words j) := by
  have atRow := slab_read (fun p : Party F=>(p.kind ar).words) G.rows i j
  have lo : 7*i.val+j.val<(G.rows.flatMap fun p=>List.ofFn (p.kind ar).words).length :=
    (List.getElem?_eq_some_iff.mp atRow).choose
  simpa only [Grid.words,List.getElem?_append_left lo] using atRow

private theorem slab_length {α β : Type*} (xs : List α) (k : ℕ) (f : α→Fin k→β) :
    (xs.flatMap fun x=>List.ofFn (f x)).length=k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_ofFn,ih,List.length_cons,Nat.mul_succ]
    exact Nat.add_comm _ _

omit [Field F] in
theorem Grid.port_word (G : Grid F) (ar : ℕ) (i : Fin G.rows.length) (j : Fin G.stride) :
    (G.words ar)[7*G.rows.length+(G.stride*i.val+j.val)]?=
      some ((G.rows.get i).port.at G.demand G.supply j.val) := by
  have length := slab_length G.rows 7 (fun p=>(p.kind ar).words)
  have atRow := slab_read (fun (p : Party F) (k : Fin G.stride)=>p.port.at G.demand G.supply k.val) G.rows i j
  dsimp only [Grid.words]
  rw [←length,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  exact atRow


omit [Field F] in
theorem grid_words_length (G : Grid F) (ar : ℕ) : (G.words ar).length=G.size := by
  classical
  unfold Grid.words Grid.size
  rw [List.length_append, slab_length, slab_length, Nat.add_mul]

def gridStart (B : PhysicalStage.Block F) (start height : ℕ) :=
  start+StableCompactROMNative.size height+staticSize B+HistoryCompactorCounts.size height

omit [Field F] [Fintype F] in
theorem roster_member (pre tail : List (Grid F)) (g : Grid F) (start : ℕ) :
    g.family (start+(pre.map Grid.size).sum) ∈ familiesFrom start (pre++g::tail) := by
  induction pre generalizing start with
  | nil => simp [familiesFrom]
  | cons a pre ih =>
    apply List.mem_cons_of_mem
    simpa [List.sum_cons,Nat.add_assoc] using ih (start+a.size)

omit [Field F] in
private theorem prefix_length (xs : List (Grid F)) (ar : ℕ) :
    (xs.flatMap fun g=>g.words ar).length=(xs.map Grid.size).sum := by
  induction xs with
  | nil => rfl
  | cons g gs ih => simp [grid_words_length,ih]

theorem stored_grid (B : PhysicalStage.Block F) {height W start : ℕ} {m : Memory W}
    (mounted : ∀ q : Fin (libraryWords B height),m (start+q.val)=data B height W q)
    (pre tail : List (Grid F)) (g : Grid F) (all : grids B=pre++g::tail)
    (j : Fin g.size) :
    m (gridStart B start height + (pre.map Grid.size).sum + j.val) =
      ((g.words (arity B))[j.val]?.getD 0 : ℕ) := by
  let n := StableCompactROMNative.size height
  let l := staticSize B
  let c := HistoryCompactorCounts.size height
  let a := (pre.map Grid.size).sum
  have hj := j.isLt
  have cut : a+g.size≤gridSize B := by simp [gridSize,all,a]
  have whole : n+l+c+(a+j.val)<libraryWords B height := by unfold libraryWords;dsimp [n,l,c];omega
  let ix : Fin (libraryWords B height) := ⟨n+l+c+(a+j.val),whole⟩
  have fetch := mounted ix
  have hn : ¬ix.val<n := by dsimp [ix];omega
  have hl : ¬ix.val-n<l := by dsimp [ix];omega
  have hc : ¬ix.val-n-l<c := by dsimp [ix];omega
  have off : ix.val-n-l-c=a+j.val := by dsimp [ix];omega
  change m (start+ix.val)=(if h : ix.val<n then _ else if h : ix.val-n<l then _
    else if h : ix.val-n-l<c then _ else _) at fetch
  rw [dite_eq_right hn,dite_eq_right hl,dite_eq_right hc,off,all,List.flatMap_append,List.flatMap_cons] at fetch
  have len := prefix_length pre (arity B)
  change (pre.flatMap fun g=>g.words (arity B)).length=a at len
  have in' : j.val<(g.words (arity B)).length := by rw [grid_words_length];exact j.isLt
  rw [List.getElem?_append_right (by omega),len,Nat.add_sub_cancel_left,List.getElem?_append_left in'] at fetch
  simpa [gridStart,ix,n,l,c,a,Nat.add_assoc] using fetch


namespace Mounted
variable {B : PhysicalStage.Block F} {height W start n p : ℕ} {m : Memory W}
  (M : Mounted B height W start m) {G : Grid F} {pre tail : List (Grid F)} {f : Fin n→Fin p→Party F}
  (page : grids B=pre++G::tail) (rows : G.rows=grid f)

def base (B : PhysicalStage.Block F) (height start : ℕ) (pre : List (Grid F)) :=
  gridStart B start height+(pre.map Grid.size).sum

include M page rows in
theorem kindAt (i : Fin n) (j : Fin p) (word : Fin 7) :
    m ((G.family (base B height start pre)).kinds+
      7*(i.val*p+j.val)+word.val)=(((f i j).kind (arity B)).words word:Word W) := by
  let row:=i.val*p+j.val
  have atRow : G.rows[row]?=some (f i j) := by
    simpa only [rows,row,Nat.mul_comm i.val p] using grid_row f i j
  obtain ⟨valid,cell⟩:=List.getElem?_eq_some_iff.mp atRow
  let pos:Fin G.rows.length:=⟨row,valid⟩
  have slot : 7*row+word.val<G.size := by
    have hw:=word.isLt
    have a : 7*row+word.val<7*G.rows.length := by omega
    exact a.trans_le (Nat.mul_le_mul_right _ (by omega:7≤7+G.stride))
  have get:=stored_grid B M.words pre tail G page ⟨_,slot⟩
  have c:=G.kind_word (arity B) pos word
  rw [show G.rows.get pos=f i j from cell] at c
  change (G.words (arity B))[7*row+word.val]?=some _ at c
  rw [c] at get
  simpa [base,Grid.family,Nat.add_assoc,pos,row] using get

include M page rows in
theorem portAt (i : Fin n) (j : Fin p) (word : Fin G.stride) :
    m ((G.family (base B height start pre)).ports+
      G.stride*(i.val*p+j.val)+word.val)=((f i j).port.at G.demand G.supply word.val:Word W) := by
  let row:=i.val*p+j.val
  have atRow : G.rows[row]?=some (f i j) := by
    simpa only [rows, row, Nat.mul_comm i.val p] using grid_row f i j
  obtain ⟨valid,cell⟩:=List.getElem?_eq_some_iff.mp atRow
  let pos:Fin G.rows.length:=⟨row,valid⟩
  have last : G.stride*row+word.val < G.stride*G.rows.length := by
    calc
      _<G.stride*row+G.stride:=Nat.add_lt_add_left word.isLt _
      _=G.stride*(row+1):=by rw [Nat.mul_succ]
      _≤G.stride*G.rows.length:=Nat.mul_le_mul_left _ valid
  let k:=7*G.rows.length+(G.stride*row+word.val)
  have bound:k<G.size := by dsimp [k,Grid.size];rw [Nat.add_mul];omega
  have get:=stored_grid B M.words pre tail G page ⟨k,bound⟩
  have c:=G.port_word (arity B) pos word
  rw [show G.rows.get pos=f i j from cell] at c
  change (G.words (arity B))[k]?=some _ at c
  rw [c] at get
  simpa [base,Grid.family,k,row,Nat.add_assoc] using get

/-- In the gather's word arithmetic the selected page is mounted at the literal location
of the selected tile and raw party; the pointer formula is independent of gate count. -/
theorem selected_pages (A : HistoryGatherBody.Layout) (i : Fin n) (j : Fin p)
    (kindBase : A.party.kinds=(G.family (base B height start pre)).kinds)
    (portBase : A.catalogue=(G.family (base B height start pre)).ports)
    (demand : A.demandCap=G.demand) (supply : A.supplyCap=G.supply) (digits : A.digitCap=G.digits)
    (parties : A.party.parties=p) (atParty : A.party.party=j.val)
    (incident : HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 2=(i.val:Word W)) :
    let R:=HistoryGatherBody.selected A m
    let g:=G.family (base B height start pre)
    R.kindPage=((g.kinds+7*(i.val*p+j.val):ℕ):Word W) ∧
      R.portPage=((g.ports+G.stride*(i.val*p+j.val):ℕ):Word W) := by
  change ((A.party.kinds:Word W)+7*(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 2*
    (A.party.parties:Word W)+(A.party.party:Word W))=_ ∧
    (A.catalogue:Word W)+(HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap:Word W)*
      (HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 2*
          (A.party.parties:Word W)+(A.party.party:Word W))=_)
  rw [incident,kindBase,portBase,demand,supply,digits,parties,atParty]
  simp [Grid.stride,Nat.cast_add,Nat.cast_mul]

end Mounted


theorem stored_compactor (B : PhysicalStage.Block F) {height W start : ℕ} {m : Memory W}
    (mounted : ∀ q : Fin (libraryWords B height),m (start+q.val)=data B height W q) :
    StableCompactROMNative.Stores height start (fun t : (Fin 3→Bool)→F => (Fintype.equivFin _ t).val) m := by
  apply StableCompactROMNative.stores_of_read
  intro q
  have h : q.val < libraryWords B height := by unfold libraryWords; omega
  simpa only [data,dite_eq_left q.isLt] using mounted ⟨q.val,h⟩

theorem stored_scalar (B : PhysicalStage.Block F) {height W start : ℕ} {m : Memory W}
    (mounted : ∀ q : Fin (libraryWords B height),m (start+q.val)=data B height W q) :
    (HistoryStaticArchive.all F (arity B)).Stores (start+StableCompactROMNative.size height) m := by
  intro q
  let n := StableCompactROMNative.size height
  have hq : q.val<staticSize B := q.isLt
  have h : n+q.val<libraryWords B height := by unfold libraryWords; dsimp [n]; omega
  have hn : ¬ n+q.val<n := by omega
  simpa [data,←Nat.add_assoc,n,staticSize] using mounted ⟨n+q.val,h⟩

theorem stored_counts (B : PhysicalStage.Block F) {height W start : ℕ} {m : Memory W}
    (mounted : ∀ q : Fin (libraryWords B height),m (start+q.val)=data B height W q)
    (q : Fin (HistoryCompactorCounts.size height)) :
    m (start+StableCompactROMNative.size height+staticSize B+q.val)=HistoryCompactorCounts.data F height q := by
  let n := StableCompactROMNative.size height
  let l := staticSize B
  have h : n+l+q.val<libraryWords B height := by unfold libraryWords; dsimp [n,l]; omega
  let j : Fin (libraryWords B height) := ⟨n+l+q.val,h⟩
  have hn : ¬j.val<n := by dsimp [j]; omega
  have hl : ¬j.val-n<l := by dsimp [j]; omega
  have eqn : j.val-n-l=q.val := by dsimp [j]; omega
  have hc : j.val-n-l<HistoryCompactorCounts.size height := by rw [eqn]; exact q.isLt
  have out := mounted j
  change m (start+j.val) = (if h : j.val<n then _ else if h : j.val-n<l then _
    else if h : j.val-n-l<HistoryCompactorCounts.size height then _ else _) at out
  rw [dite_eq_right hn,dite_eq_right hl,dite_eq_left hc] at out
  simpa only [j,n,l,←Nat.add_assoc] using out.trans
    (congrArg (HistoryCompactorCounts.data F height) (Fin.ext eqn))



end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
