import OAI.ThreeFlat.RAM.TickTerminalRootRun
import OAI.ThreeFlat.RAM.TickTerminalRecords
import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Word-size bounds for running one selected terminal root -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Diagonal.TickWorkspace

/-- The completed root records remain in S13, pointing to S12. Once the interior traversal has
returned, the remaining areas S14–18 are available for the single selected slot. S9 is the
actual metadata area consumed by the weighted machine. -/
def mounted (u p wireStart wirePrefix : ℕ) : Arena where
  control := base u 18
  selected := base u 17
  rootHeader := TickPhysicalABI.directory u 3
  results := base u 13
  wireStart := wireStart
  wirePrefix := wirePrefix
  physicalPins := p
  metadata := base u 9
  seed := base u 14
  map := base u 14+64
  commands := base u 15
  arguments := base u 16

open Computability.VPVNP.BurstRAM PrivateRAM HistoryTerminalTape PhysicalPinsExpr DescriptorScan TickTerminalPrimitive
open Diagonal.TickWorkspace HistoryJoinScan
open scoped Fin.CommRing

open private rd seedList pick header_rows input_reads input_seed from OAI.ThreeFlat.RAM.TickTerminalRootRun
open private h entry piece switch from OAI.ThreeFlat.RAM.HistoryTerminalTape

private theorem seedPickFits {W : ℕ} (mu : ℕ→ℕ) (vs : Fin 1→ℕ) (e : Formula 1)
    (f : e.Fits W (fun _=>0) mu vs) (v : e.natural W (fun _=>0) mu vs<2^W)
    (s : ℕ) (xs : List (Formula 1)) (size : s+xs.length≤2^W)
    (valid : ∀ t∈xs,t.Fits W (fun _=>0) mu vs) :
    (pick s xs e).Fits W (fun _=>0) mu vs := by
  induction xs generalizing s with
  | nil => trivial
  | cons x xs ih =>
    change _ ∧ True ∧ _ ∧ s<2^W ∧ _
    have len : s+1+xs.length≤2^W := by simp only [List.length_cons] at size; omega
    refine ⟨f,trivial,v,by omega,?_⟩
    split
    · exact valid x (List.mem_cons_self ..)
    · exact ih (s+1) len (fun t ht=>valid t (List.mem_cons_of_mem _ ht))

/-- The seed expression tests its small column and reads only the six compact-directory
intervals in bootReads. Arbitrary words in the output currently under construction are allowed. -/
private theorem boot_fits_reads {W : ℕ} (A : Arena) (mu : ℕ→ℕ) (z : Word W)
    (seed : A.seed+26<2^W) (addr : ∀ j,bootReads A mu j → j<2^W) :
    (boot A).Fits W (fun _=>0) mu (fun _=>z.val) := by
  have width : W ≠ 0 := by rintro rfl; simp at seed
  have controls : A.control+3 < 2^W := addr _ (Or.inl ⟨by omega,by omega⟩)
  have headers : A.rootHeader+1 < 2^W := addr _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
  have selected : A.selected+mu A.control < 2^W := addr _ (Or.inr (Or.inr (Or.inl rfl)))
  have results : A.results+8*rootId A mu+5 < 2^W :=
    addr _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))
  have pointer : mu (A.rootHeader+1)+8*rootId A mu+6 < 2^W :=
    addr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have incident : mu (mu (A.rootHeader+1)+8*rootId A mu+6)+1 < 2^W :=
    addr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩)))))
  unfold rootId at results pointer incident
  apply seedPickFits
  · exact ⟨trivial,trivial,z.isLt,by change A.seed < 2^W; omega⟩
  · change z.val-A.seed<2^W
    have := z.isLt
    omega
  · change 0+26≤2^W
    omega
  · intro t ht
    simp only [seedList,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst t <;>
      simp [rd,add,mul,Formula.Fits,Formula.natural,natOp,opFits] <;>
      repeat' apply And.intro
    all_goals first | assumption | omega

private theorem bootReads_eq (A : Arena) (m mu : ℕ→ℕ)
    (same : ∀ j,bootReads A m j → mu j=m j) : bootReads A mu=bootReads A m := by
  have c : mu A.control=m A.control := same _ (Or.inl ⟨le_rfl,by omega⟩)
  have h : mu A.rootHeader=m A.rootHeader := same _ (Or.inr (Or.inl ⟨le_rfl,by omega⟩))
  have h' : mu (A.rootHeader+1)=m (A.rootHeader+1) := same _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
  have sel := same _ (Or.inr (Or.inr (Or.inl rfl)))
  have node : rootId A mu=rootId A m := by simp [rootId,c,h,sel]
  have nested := same _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  funext j
  simp only [bootReads,c,h',node,nested]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
/-- The row generator needs fit only on the half and wire-prefix addresses read by its selected
branch. All other values may fill the word, including endpoint pointers in unrelated rows. -/
private theorem row_fits_reads {W : ℕ} (A : Arena) (T : Root) (mu raw : ℕ→ℕ)
    (cmd : Bool) (i : ℕ) (j : Fin 7) (ix : i<T.halves+2)
    (seed : A.seed+26<2^W) (span : 7*(T.halves+2)<2^W)
    (hdr : ∀ c : Fin 14,mu (A.seed+8+c.val)=T.words c)
    (values : ∀ c : Fin 14,T.words c<2^W)
    (readable : ∀ z,rangeReads T raw z → z<2^W)
    (same : ∀ z,rangeReads T raw z → mu z=raw z) :
    (HistoryTerminalTape.formula cmd).Fits W (fun _=>0) mu (genInput A (7*i+j.val)) := by
  have width : W ≠ 0 := by rintro rfl; simp at seed
  have late : (T.halves < i) ↔ ¬ i ≤ T.halves := by omega
  have hj := j.isLt
  have row : (7*i+j.val)/7=i := by
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt hj,Nat.zero_add]
  have col : (7*i+j.val)%7=j.val := by rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  have hv (k : ℕ) (hk : k<14) : mu (A.seed+8+k)=T.words ⟨k,hk⟩ := hdr ⟨k,hk⟩
  have hv' (k : ℕ) (hk : k<14) : A.seed+8+k<2^W := by omega
  have ent (k l : ℕ) (hk : k<T.halves) (hl : l<4) :
      T.halfData+4*k+l<2^W := readable _ (Or.inl ⟨by omega,by omega⟩)
  have edge (k : ℕ) (hk : k<T.halves) : mu (T.halfData+4*k)= (half T raw k).edge :=
    same _ (Or.inl ⟨by omega,by omega⟩)
  have wire (k : ℕ) (hk : k<T.halves) : T.wirePrefix+(half T raw k).edge<2^W :=
    readable _ (Or.inr ⟨k,hk,rfl⟩)
  have headerLt := values (4 : Fin 14)
  change T.halves<2^W at headerLt
  by_cases zero : i=0 <;> by_cases active : i≤T.halves <;> cases cmd <;> fin_cases j <;>
    simp (config:={decide:=true}) [HistoryTerminalTape.formula,switch,
      piece,entry,h,genInput,Formula.Fits,
      Formula.natural,natOp,natTest,opFits,row,col,hv,Root.words,late,zero,active,width] <;>
    repeat' first | constructor | assumption | omega | apply ent <;> omega |
      rw [edge _ (by omega)]; apply wire; omega
  exact ent (i-1) 0 (by omega) (by decide)

private theorem shift_val {W : ℕ} (s d : ℕ) (a : Word W) (lo : d≤a.val)
    (fit : s+(a.val-d)<2^W) : ((s:Word W)+(a-(d:Word W))).val=s+(a.val-d) := by
  calc
    ((s:Word W)+(a-(d:Word W))).val = ((s:Word W)+((a.val:Word W)-(d:Word W))).val := by rw [Fin.cast_val_eq_self]
    _ = s+(a.val-d) := by rw [←Nat.cast_sub lo,←Nat.cast_add,Fin.val_cast_of_lt fit]

/-- The translated source and optional pin lookup stay in the old stream and the newly generated
pin map, respectively. Their contents need not satisfy a range predicate. -/
private theorem separate_join {W : ℕ} (T : Root) (m : Memory W)
    (header : fetch (joinArgument T : Word W) m=(joinHeader T).words)
    (argsFit : T.arguments+7*(T.halves+2)≤2^W)
    (argsAfter : T.meta+4*T.rows≤T.arguments)
    (streamFit : T.stream+4*T.rows≤2^W) (inputs : T.stream+4*T.rows≤T.meta ∨ T.meta+4*T.rows≤T.stream)
    (mapFit : T.map+T.localPins≤2^W) (mapAfter : T.meta+4*T.rows≤T.map)
    (small : 2+T.localPins<2^W) :
    Separate (joinArgument T : Word W) T.meta (T.meta+4*T.rows) m := by
  constructor
  · intro j
    have hj := j.isLt
    have fit : joinArgument T+j.val<2^W := by unfold joinArgument; omega
    change ((joinArgument T:Word W)+(j.val:Word W)).val<T.meta ∨ T.meta+4*T.rows≤((joinArgument T:Word W)+(j.val:Word W)).val
    rw [←Nat.cast_add,Fin.val_cast_of_lt fit]
    right; unfold joinArgument; omega
  · intro a lo hi
    dsimp only
    rw [header]
    change ((T.stream:Word W)+(a-(T.meta:Word W))).val<T.meta ∨ T.meta+4*T.rows≤((T.stream:Word W)+(a-(T.meta:Word W))).val
    rw [shift_val _ _ _ lo (by omega)]
    omega
  · intro a lo hi
    dsimp only
    rw [header]
    let x := m ((T.stream:Word W)+(a-(T.meta:Word W))).val
    change ¬x<2 → x<2+(T.localPins:Word W) → ((T.map:Word W)+(x-2)).val<T.meta ∨ T.meta+4*T.rows≤((T.map:Word W)+(x-2)).val
    intro low high
    have two : (2:Word W).val=2 := Fin.val_cast_of_lt (by omega : 2<2^W)
    change ¬x.val<(2:Word W).val at low
    change x.val<(2+(T.localPins:Word W)).val at high
    rw [two] at low
    rw [show (2:Word W)=((2:ℕ):Word W) by norm_num,←Nat.cast_add,Fin.val_cast_of_lt small] at high
    rw [show (2:Word W)=((2:ℕ):Word W) by norm_num,shift_val _ _ _ (by omega) (by omega)]
    omega

/-- An immutable read interval is below the first mutable root bank or above the last one.
Both S11–13 compact data and S38–51 navigation/archive data obey this separation. -/
def ImmutableBankAt (W u start count : ℕ) := (start+count≤base u 14 ∨ base u 18+stride u≤ start) ∧
  start+count≤2^W

private theorem ImmutableBankAt.word {W u start count j : ℕ} (h : ImmutableBankAt W u start count)
    (low : start≤j) (high : j<start+count) :
    (j<base u 14 ∨ base u 18+stride u≤j) ∧ j<2^W := by
  obtain ⟨sep,cap⟩ := h
  omega

/-- Sizes and pointer ranges of one selected compact root. These are the locations of its
directory entries, generated rows and per-port offsets in the actual S9/S12–18 banks. -/
structure CompactRootAt {W : ℕ} (u p wireStart wirePrefix : ℕ) (m : Memory W) : Prop where
  space : 65≤ stride u
  publicWords : p<2^W ∧ wireStart<2^W ∧ wirePrefix<2^W
  selected : natMemory m (base u 18)<stride u
  resultWords : let A:=mounted u p wireStart wirePrefix
    A.results+8*rootId A (natMemory m)+6≤A.seed
  halfPointer : let A:=mounted u p wireStart wirePrefix
    ImmutableBankAt W u (natMemory m (A.rootHeader+1)+8*rootId A (natMemory m)+6) 1
  halfHeader : let A:=mounted u p wireStart wirePrefix
    ImmutableBankAt W u (natMemory m (natMemory m (A.rootHeader+1)+8*rootId A (natMemory m)+6)) 2
  halfData : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    ∀ j<4*T.halves, ImmutableBankAt W u (T.halfData+j) 1
  «prefix» : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    ∀ i<T.halves,ImmutableBankAt W u (wirePrefix+(HistoryTerminalTape.half T (natMemory m) i).edge) 1
  tableWords : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    7*(T.halves+2)≤ stride u
  mapWords : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    64+T.localPins≤ stride u
  span : PinSpan (terminal (mounted u p wireStart wirePrefix) (natMemory m)) (natMemory m)
  endpoints : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    T.endpoints+T.ext≤base u 14
  metadata : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    T.meta+4*T.rows≤base u 9+stride u
  stream : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    base u 10≤T.stream ∧ T.stream+4*T.rows≤base u 14

/-- The native root interpreter fits in any physical word carrying the end of S18. -/
theorem CompactRootAt.bounds {W u p wireStart wirePrefix : ℕ}
    (cap : base u 18+stride u<2^W) {m : Memory W} (compact : CompactRootAt u p wireStart wirePrefix m) :
    RootBounds (mounted u p wireStart wirePrefix) m := by
  let A := mounted u p wireStart wirePrefix
  let mu := natMemory m
  let T := terminal A mu
  let c : Word W := ((A.seed+5 : ℕ):Word W)
  have wide := compact.space
  have b9 := apart (u:=u) (by decide : 9<10)
  have b10 := apart (u:=u) (by decide : 10<11)
  have b11 := apart (u:=u) (by decide : 11<14)
  have b14 := apart (u:=u) (by decide : 14<15)
  have b15 := apart (u:=u) (by decide : 15<16)
  have b16 := apart (u:=u) (by decide : 16<17)
  have b17 := apart (u:=u) (by decide : 17<18)
  have seed : A.seed=base u 14 := rfl
  have targ : T.arguments=base u 16 := rfl
  have tbl : A.commands=base u 15 := rfl
  have args : A.arguments=base u 16 := rfl
  have pm : T.map=base u 14+64 := rfl
  have cf : A.control=base u 18 := rfl
  have sel : A.selected=base u 17 := rfl
  have first : A.seed+26≤A.commands := by omega
  have sw : A.seed+26<2^W := by omega
  have fc : c.val=A.seed+5 := Fin.val_cast_of_lt (by omega)
  have count : 7*(T.halves+2)≤ stride u := compact.tableWords
  have mapsize : 64+T.localPins≤ stride u := compact.mapWords
  have gap : A.commands+7*(T.halves+2)≤A.arguments := by omega
  have endArg : A.arguments+7*(T.halves+2)<2^W := by omega
  have me : T.meta+4*T.rows≤base u 9+stride u := compact.metadata
  have st : base u 10≤T.stream ∧ T.stream+4*T.rows≤base u 14 := compact.stream
  have endpoints : T.endpoints+T.ext≤base u 14 := compact.endpoints
  have endpointBound := compact.span.endpoints
  change T.ext≤T.localPins at endpointBound
  have hword (i : Fin 14) : T.words i<2^W := by
    obtain ⟨h0,h1,h2⟩ := compact.publicWords
    have argsLo : T.arguments<2^W := by omega
    have mapLo : T.map<2^W := by omega
    have metaLo : T.meta<2^W := by omega
    fin_cases i <;> first
      | exact argsLo
      | exact mapLo
      | exact metaLo
      | exact h0
      | exact h1
      | exact h2
      | exact (m _).isLt
  have readLoc (j : ℕ) (h : rangeReads T mu j) :
      (j<A.seed ∨ base u 18+stride u≤j) ∧ j<2^W := by
    obtain h|⟨i,hi,rfl⟩ := h
    · have atWord : ImmutableBankAt W u (T.halfData+(j-T.halfData)) 1 :=
        compact.halfData (j-T.halfData) (show j-T.halfData < 4*T.halves by omega)
      have eqn : T.halfData+(j-T.halfData)=j := by omega
      rw [eqn] at atWord
      exact atWord.word le_rfl (by omega)
    · have atWord : ImmutableBankAt W u (T.wirePrefix+(HistoryTerminalTape.half T mu i).edge) 1 :=
        compact.prefix i hi
      exact atWord.word le_rfl (Nat.lt_succ_self _)
  have imm : sourceSafe T mu A.seed (A.seed+26) := by
    intro j hj
    have := (readLoc _ hj).1
    omega
  have immutableC : sourceSafe T mu A.commands (A.commands+7*(T.halves+2)) := by
    intro j hj
    have := (readLoc _ hj).1
    omega
  have immutableA : sourceSafe T mu A.arguments (A.arguments+7*(T.halves+2)) := by
    intro j hj
    have := (readLoc _ hj).1
    omega
  have bootLoc (z : ℕ) (h : bootReads A mu z) : (z<A.seed ∨ A.seed+26≤z) ∧ z<2^W := by
    have selHi : mu A.control<stride u := compact.selected
    have rowsHi : A.results+8*rootId A mu+6≤A.seed := compact.resultWords
    have ptrRange : ImmutableBankAt W u (mu (A.rootHeader+1)+8*rootId A mu+6) 1 := compact.halfPointer
    have incRange : ImmutableBankAt W u (mu (mu (A.rootHeader+1)+8*rootId A mu+6)) 2 := compact.halfHeader
    have root : A.rootHeader=base u 11+3*(stride u/4) := rfl
    change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ at h
    rcases h with h|h|h|h|h|h
    · omega
    · omega
    · omega
    · omega
    · have := ptrRange.word (j:=z) (by omega) (by omega)
      omega
    · have := incRange.word h.1 h.2
      omega
  have baseDisj (cmd : Bool) : A.seed+26≤tableBase A cmd := by
    cases cmd <;> simp [tableBase] <;> omega
  have lim : TableBounds A m := by
    refine ⟨first,gap,endArg,hword,imm,immutableC,immutableA,?_⟩
    intro cmd i hi j v frame
    have sh (k : Fin 26) : v (A.seed+k.val)=(seedWords A mu k:Word W) := by
      have hk := k.isLt
      have safe := baseDisj cmd
      rw [frame _ (Or.inl (by omega))]
      exact input_seed A m cmd first k
    have preserved (z : ℕ) (hz : rangeReads T mu z) : natMemory v z=mu z := by
      have sep : z<tableBase A cmd ∨ tableBase A cmd+7*(T.halves+2)≤z := by
        cases cmd
        · exact immutableA z hz
        · exact immutableC z hz
      exact (congrArg Fin.val (frame _ sep)).trans (input_reads A m cmd imm immutableC _ hz)
    exact row_fits_reads A T (natMemory v) mu cmd i j hi sw (by omega)
      (header_rows A m v sh hword) hword (fun z hz=>(readLoc z hz).2) preserved
  have pinRange (i : ℕ) (hi : i<T.halves+1) :
      let x:=pinJob T mu (readyImage A m) i
      T.map≤x.start ∧ x.finish≤T.map+T.localPins := by
    cases i with
    | zero => change T.map≤T.map ∧ T.map+T.ext≤_; omega
    | succ i =>
      change T.map≤ interval T mu i ∧ interval T mu i+(HistoryTerminalTape.half T mu i).width≤_
      have h := compact.span.halves i (show i < T.halves by omega)
      change T.ext+(HistoryTerminalTape.half T mu i).start+(HistoryTerminalTape.half T mu i).width≤T.localPins at h
      unfold interval
      omega
  have joinsafe : PinBanks T c := by
    constructor
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  change RootBounds A m
  refine { toTableBounds := lim, controlFit := ?_, saveApart := ?_,
           bootApart := fun z hz => (bootLoc z hz).1, bootFits := ?_,
           endpointFit := ?_, endpointApart := ?_, pinOutputs := ?_,
           rowOutput := ?_, joinApart := ?_ }
  · omega
  · exact Or.inr (by omega)
  · intro z hlo hhi v frame
    have same (b : ℕ) (hb : bootReads A mu b) : natMemory v b=mu b :=
      congrArg Fin.val (frame _ (bootLoc b hb).1)
    apply boot_fits_reads A (natMemory v) z sw
    intro j hj
    rw [bootReads_eq A mu (natMemory v) same] at hj
    exact (bootLoc j hj).2
  · change T.endpoints+T.ext ≤ 2^W
    omega
  · change ∀ z, T.endpoints≤z → z<T.endpoints+T.ext → Outside T.map (T.map+T.ext) z
    intro z lo hi
    exact Or.inl (by omega)
  · change ∀ i, i<T.halves+1 →
      let x := pinJob T mu (readyImage A m) i
      Protected T A.commands c x.start x.finish ∧ x.finish<2^W
    intro i hi
    let x := pinJob T mu (readyImage A m) i
    change Protected T A.commands c x.start x.finish ∧ x.finish<2^W
    have range : T.map≤x.start ∧ x.finish≤T.map+T.localPins := pinRange i hi
    refine ⟨⟨Or.inr (by omega),Or.inl (by omega),Or.inl (by omega)⟩,?_⟩
    omega
  · change Protected T A.commands c T.meta (T.meta+4*T.rows) ∧ T.meta+4*T.rows<2^W
    refine ⟨⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,?_⟩
    omega
  · change Separate (joinArgument T : Word W) T.meta (T.meta+4*T.rows)
      (pinMemory T mu c (readyImage A m))
    apply separate_join T _ (fetch_join T mu c (readyImage A m) A.commands
      (loaded_tables A m gap) (by omega) compact.span joinsafe)
    · omega
    · omega
    · omega
    · exact Or.inr (by omega)
    · omega
    · omega
    · omega

end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
