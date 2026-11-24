import OAI.Computability.VPVNP.CompressorChoiceGrid
import OAI.Computability.VPVNP.RAMParameters
import OAI.Computability.VPVNP.PrimedCounterRenameRun

/-!
# Executing rounded-grid selection and outer term choice on demand records

The demand scanner and the fixed grid tests share a register file in one
compiled call. The call returns the first covering grid row. The term reader
computes its repetition count from the same demand records and chooses the
outer supply vector. The code uses the ordered grid fixed by Theorem 6.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandGridRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter

variable {w r l k : ℕ}

/-- The two fixed tables share a register file and occupy disjoint parts of
the public constants. Their normal control edge is the sequence instruction
link, so no dynamic memory entry is supplied for the energy. -/
def join (left : Flow r l) (right : Flow r k) : Flow r (l+k) :=
  .seq (renameFlow id (Fin.castAdd k) left) (renameFlow id (Fin.natAdd l) right)

private theorem widen {v K : ℕ} (a : Flow r v) (idx : Fin v → Fin K) (data : Fin K → Word w)
    (values : Fin v → Word w) (hval : data ∘ idx = values)
    {state : Word w} {rs mid : Regs w r} {mem mem' : Memory w} {es : List (Event w)}
    (h : Flow.Exec values state a rs mem es mid mem') :
    Flow.Exec data state (renameFlow id idx a) rs mem es mid mem' := by
  obtain ⟨out, hr, ha, _⟩ := liftExec (Function.Embedding.refl (Fin r)) idx data
    (hval ▸ h) rs rfl
  change out = mid at ha
  exact ha ▸ hr

theorem join_exec {left : Flow r l} {right : Flow r k} {p : Fin l → Word w} {q : Fin k → Word w}
    {state : Word w} {rs mid out : Regs w r} {m m' m'' : Memory w} {es fs : List (Event w)}
    (h₁ : Flow.Exec p state left rs m es mid m') (h₂ : Flow.Exec q state right mid m' fs out m'') :
    Flow.Exec (Fin.append p q) state (join left right) rs m (es ++ fs) out m'' := by
  apply Flow.Exec.seq
  · exact widen left (Fin.castAdd k) _ p (funext fun i => Fin.append_left ..) h₁
  · exact widen right (Fin.natAdd l) _ q (funext fun i => Fin.append_right ..) h₂


variable {D : Type*} [Fintype D] {d t : ℕ}

/-- Instruction sequence that prepares the demand energy before scanning the candidate grid
rows. -/
def code (order : Fin d ≃ D) (rows : Fin t → D → ℚ) :=
  join (DemandPreparation.energyPrefix d) (GridRAM.grid order rows)

/-- Instantiate the demand-grid program with the chosen demand order, energy weights and
candidate-row coefficients. -/
def machine (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ) (w : ℕ) :=
  ((code order rows).template (some 1)).instantiate w
    (Fin.append (DemandPreparation.publicWords order p 1 w) (GridRAM.coefficients order p rows))

/-- This call begins at the ordinary machine entry point. Its return word
indexes the same first covering point as the mathematical grid search. -/
theorem native (order : Fin d ≃ D) (p : D → ℚ) (rows : Fin t → D → ℚ) :
    ∃ K : ℕ, ∀ M w, K + 4*Nat.clog 2 (M+1) ≤ w → ∀ (addr : Word w) (mem : Memory w),
      (∀ i, DemandPreparation.demandAt order addr mem i ≤ M) →
      let prog := machine order p rows w
      let b := DemandPreparation.demandAt order addr mem
      let fuel := 6*d + (11*d+4)*t + 8
      ∃ es, execute prog.program fuel (prog.program.start addr) mem [] =
        some ⟨es, some (Fin.ofNat _ (GridRAM.firstRow p b rows))⟩ ∧
        choiceBits es = [] ∧ countProbes es ≤ d + t*d ∧ after mem es = mem ∧ es.length < fuel := by
  obtain ⟨k₀,h₀⟩ := DemandPreparation.preparation_fit p 1
  let C := GridRAM.operandConstant order p rows
  let K := max k₀ (max C.size t.size)
  refine ⟨K,fun M w hW addr mem hD => ?_⟩
  let b := DemandPreparation.demandAt order addr mem
  let pv := DemandPreparation.publicWords order p 1 w
  have hk₀ : k₀ ≤ K := le_max_left _ _
  have hC : C.size ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have ht : t.size ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨htwo,hs,_,_,hweights⟩ := h₀ M b hD
  have hp₀ := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show k₀ + 4*Nat.clog 2 (M+1) ≤ w by omega)
  have hpub (i : Fin d) : (pv i.castSucc).val = MotifAdmission.weight p (order i) := by
    simp [pv, DemandPreparation.publicWords, Nat.mod_eq_of_lt ((hweights (order i)).trans_le hp₀)]
  obtain ⟨es,mid,he,heb,hep,hem,hel,energy,_⟩ :=
    DemandPreparation.energyPrefix_exec order p pv addr mem (fun _ => 0) hpub
  have heval : (mid 0).val = MotifAdmission.energy p b := by
    rw [energy]; apply Nat.mod_eq_of_lt
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans_lt (hs.trans_le hp₀)
  have hbox : C*(M+1)^2 < 2^w := by
    apply lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show C.size + 2*Nat.clog 2 (M+1) ≤ w by omega))
    rw [pow_add, Nat.mul_comm 2, pow_mul]
    exact mul_lt_mul_of_lt_of_le_of_pos_of_nonneg (Nat.lt_size_self _) (Nat.pow_le_pow_left
      (Nat.le_pow_clog (by decide) _) 2) (pow_pos (Nat.succ_pos _) _) (Nat.zero_le _)
  obtain ⟨fs,out,hg,hgb,hgp,hgm,hgl,ho⟩ := GridRAM.grid_exec order p rows addr mem mid heval
    ((by decide : 1 < 2).trans (htwo.trans_le hp₀)) (Nat.size_le.mp (by omega))
    (GridRAM.operandsFit_of_width order p rows b M hD hbox)
  let budget := 6*d + (11*d+4)*t + 7
  have hl : (es ++ fs).length ≤ budget := by simp only [List.length_append,hel]; dsimp [budget]; omega
  have hb : choiceBits (es++fs) = [] := by simp [Flow.choiceBits_append,heb,hgb]
  have hrun := DemandPreparation.execute_return (code order rows) (Fin.append pv (GridRAM.coefficients order p rows))
    1 addr mem mem (es++fs) out (join_exec he hg) hb budget hl
  have ho' : out 1 = Fin.ofNat _ (GridRAM.firstRow p b rows) := by rw [← ho]; simp
  refine ⟨es++fs,ho' ▸ hrun,hb,?_,?_,by change _ < budget+1; omega⟩
  · rw [DemandPreparation.probes_append, hep]
    exact Nat.add_le_add_left hgp d
  · rw [show after mem (es++fs) = after (after mem es) fs from List.foldl_append, hem, hgm]


open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k₀ : Type*} [Field k₀] {J D₀ S : Type} [Fintype J] [Fintype D₀] [Fintype S]
variable {a b₀ : D₀ → J} {P : Supply J S} {p : D₀ → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k₀ a b₀ P (realWidths p) (realWidths q) H H')

/-- Rows are ordered exactly as in the fixed rounded demand grid. -/
noncomputable def fixedRows : Fin B.grid.demands.toList.length → D₀ → ℚ := B.grid.demands.toList.get

theorem fixedRows_list : List.ofFn (fixedRows B) = B.grid.demands.toList := List.ofFn_get _

/-- Run the grid call followed by the demand-to-payload calls. The first
returned field identifies the fixed template used for the local maps. -/
noncomputable def chooseTerm {d n : ℕ} (order : Fin d ≃ D₀) (supply : Fin n ≃ S)
    (addr : BurstRAM.Word w) (mem : Memory w) (prepFuel : ℕ) (bits : List Bool) :
    Option (BurstRAM.Word w × Report w) := do
  let prog := machine order p (fixedRows B) w
  let fuel := 6*d + (11*d+4)*B.grid.demands.toList.length + 8
  let grid ← execute prog.program fuel (prog.program.start addr) mem []
  let row ← grid.result
  let chosen ← DemandPreparation.chooseFromDemand B order supply addr (after mem grid.events) prepFuel bits
  return (row,chosen)

/-- All dynamic motif data come from actual demand records. The three reset
calls choose the original fixed grid point and admit exactly the binary
streams of Theorem 6.1's outer indices, including its zero-width unit case. -/
theorem chooseTerm_spec {d n : ℕ} (order : Fin d ≃ D₀) (supply : Fin n ≃ S)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ M w, K + 4*Nat.clog 2 (M+1) ≤ w → ∀ (addr : BurstRAM.Word w) (mem : Memory w),
      (∀ i, DemandPreparation.demandAt order addr mem i ≤ M) →
      let demand := DemandPreparation.demandAt order addr mem
      let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
      ∃ (hw : outerCap B demand < 2^w) (row : BurstRAM.Word w),
        B.grid.demands.toList[row.val]? = some (demandGrid B hp demand).val ∧
        ∀ bits, (chooseTerm B order supply addr mem fuel bits).map Prod.fst =
          (DemandPreparation.chooseFromDemand B order supply addr mem fuel bits).map (fun _ => row) ∧
          ((chooseTerm B order supply addr mem fuel bits).isSome ↔
            ∃ v, (outerReader B supply hq demand w hw).read bits = some (v, [])) := by
  let table := B.grid.demands.toList
  let rows := fixedRows B
  obtain ⟨kG,hG⟩ := native order p rows
  obtain ⟨kC,hC⟩ := DemandPreparation.chooseFromDemand_iff B order supply hq
  refine ⟨max table.length.size (max kG kC),fun M w hW addr mem hD => ?_⟩
  let demand := DemandPreparation.demandAt order addr mem
  let idx := GridRAM.firstRow p demand rows
  have hiG := le_max_left kG kC
  have hiC := le_max_right kG kC
  have hm := le_max_right table.length.size (max kG kC)
  have hlen := le_max_left table.length.size (max kG kC)
  obtain ⟨es,hgrid,_,_,hmem,_⟩ := hG M w (by omega) addr mem hD
  obtain ⟨hw,hchoice⟩ := hC M w (by omega) addr mem hD
  have ht : table.length < 2^w := Nat.size_le.mp (by omega)
  have hidx : idx < 2^w := (List.findIdx_le_length (xs := List.ofFn rows) (p := _)).trans_lt
    (by simpa [rows,fixedRows_list,table] using ht)
  have hz := GridRAM.firstRow_getElem? p demand rows
  rw [show List.ofFn rows = table from fixedRows_list B, selectGrid_eq B hp demand] at hz
  let row : BurstRAM.Word w := Fin.ofNat _ idx
  refine ⟨hw,row,?_,fun bits => ?_⟩
  · have hv : row.val = idx := Nat.mod_eq_of_lt hidx
    rw [hv]
    exact hz
  · let fuel := 6*d + 7*((∑ i, MotifAdmission.weight p i).size + 2*Nat.clog 2 (M+1)) + 10
    have he : chooseTerm B order supply addr mem fuel bits =
        (DemandPreparation.chooseFromDemand B order supply addr mem fuel bits).map (fun r => (row,r)) := by
      dsimp only [rows] at hgrid
      simp only [chooseTerm, hgrid, bind, Option.bind_some, pure, hmem]
      cases DemandPreparation.chooseFromDemand B order supply addr mem fuel bits <;> rfl
    change _ ∧ ((chooseTerm B order supply addr mem fuel bits).isSome ↔ _)
    rw [he, Option.isSome_map]
    refine ⟨?_,hchoice bits⟩
    rw [Option.map_map]
    rfl

end CompressorRecords.DemandGridRAM

namespace CompressorRecords.DemandPreparation

/-- The fixed motif's word requirement is eventually met by the Section 9.1
machine uniformly over every polynomial bound on intermediate demand widths. -/
theorem eventually_live_word_fits (B : ℕ) (hB : 0 < B) (K L C A : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ M, M ≤ C * n^A →
      K + L * Nat.clog 2 (M+1) ≤ (BurstRAM.addressWidth B n + 10)^4 := by
  let c₀ := K + L * (C+1).size + L*A + 1
  filter_upwards [Filter.eventually_ge_atTop (2^c₀)] with n hn M hM
  let c := Nat.clog 2 n
  have hc : c₀ ≤ c := by simpa [c,Nat.clog_pow _ _ (by decide : 1 < 2)] using Nat.clog_mono_right 2 hn
  have hpos : 0 < n := (Nat.two_pow_pos c₀).trans_le hn
  have hbound : Nat.clog 2 (M+1) ≤ (C+1).size + A*c := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add, Nat.mul_comm A c, pow_mul]
    have hi : M+1 ≤ (C+1)*n^A := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add hM (pow_pos hpos _)
    exact hi.trans (Nat.mul_le_mul (Nat.lt_size_self (C+1)).le
      (Nat.pow_le_pow_left (Nat.le_pow_clog Nat.one_lt_two n) A))
  have hC : K + L * (C+1).size ≤ c := (show K + L * (C+1).size ≤ c₀ by dsimp [c₀]; omega).trans hc
  have hA : L*A ≤ c := (show L*A ≤ c₀ by dsimp [c₀]; omega).trans hc
  have hR : c ≤ BurstRAM.addressWidth B n := Nat.le_mul_of_pos_left _ hB
  calc
    K + L*Nat.clog 2 (M+1) ≤ K + L*((C+1).size + A*c) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hbound) K
    _ = (K + L * (C+1).size) + (L*A)*c := by ring
    _ ≤ c + c*c := Nat.add_le_add hC (Nat.mul_le_mul_right _ hA)
    _ ≤ (c+10)^2 := by nlinarith
    _ ≤ (BurstRAM.addressWidth B n+10)^2 := Nat.pow_le_pow_left (Nat.add_le_add_right hR _) 2
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

end CompressorRecords.DemandPreparation

end VPVNP
end Computability
end OAI
