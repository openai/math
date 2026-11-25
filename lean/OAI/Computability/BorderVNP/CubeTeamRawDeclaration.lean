import OAI.Computability.BorderVNP.CubeTeamDeclarationReturn
import OAI.Computability.BorderVNP.CubeScatterSelectorPrefix

/-! # Recovering one global selector tuple from real canonical-owner returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CellDispatch Physical Physical.Owned Tally Scatter TeamRowPrepare VPVNP.BurstRAM

variable {Team : Type*} {w n d blocks b h K s : ℕ}

/-- On a strict row its public selector word identifies every physical selector at that row.
Assignments on other rows do not enter this equality. -/
theorem equal_selectors_at {i : Fin (n+1)} {sym : Symbols d} {u v : Packet n d blocks → Selector n K h}
    (eqn : commonSelectors u i sym = commonSelectors v i sym) (p : Packet n d blocks) (row : p.1.1 i = sym) :
    u p = v p := by
  have decoded := (commonSelectors_decode u i sym).symm.trans ((congrArg
    (decodeSelectors n K h (packetVisits blocks i sym).length) eqn).trans (commonSelectors_decode v i sym))
  exact List.map_inj_left.mp (Option.some.inj decoded) p ((mem_packetVisits ..).mpr row)

/-- Raw-prefix evidence on actual scatter returns. Each canonical owner supplies its own
selector witnesses and the corresponding physically stored words; no global tuple is given. -/
structure RawScans (owner : Fin d → Team) (pub : Team → Arg → Word w)
    (mac : Team → TeamOpcode.Macros w 8) (decl : LengthDeclaration n d) (raw : Symbols d → List Bool)
    (blocks b h K s : ℕ) extends DispatchScans owner pub mac n b h K s where
  /-- The actual lower-owner strict scatter observed the received selector prefix and left
  its decoded fields in the final packet bank. -/
  strict : ∀ (p : Symbols d) {r m gs u mu},
    resident (owner p.val.1) (finProdFinEquiv p.val).val (r 7) m →
    ReadyRow (scanLayout (owner p.val.1)) (readings m) (finProdFinEquiv p.val).val (.ofWords r m) →
    Runs (pub (owner p.val.1)) (mac (owner p.val.1)) (OwnedStages.strictSide n b h K s) r m gs u mu →
    ∃ v : CheckAddresses, CheckWords blocks b h K s v (pub (owner p.val.1)) decl p.val.1 p.val.2 u mu ∧
      ∃ localSelect : Packet n d blocks → Selector n K h, raw p = commonSelectors localSelect decl.1 p ∧
        ∀ z : {z : Packet n d blocks // z.1.1 decl.1 = p}, SelectorRead.Stored (readings mu)
          (v.bank+packetIndex z.val*bankWidth n b h K s) (localSelect z.val)
  /-- Repeated-symbol scatters restore the corresponding native checker inputs. -/
  diagonal : ∀ (x : Fin d) {r m gs u mu}, resident (owner x) (finProdFinEquiv (x,x)).val (r 7) m →
    ReadyRow (scanLayout (owner x)) (readings m) (finProdFinEquiv (x,x)).val (.ofWords r m) →
    Runs (pub (owner x)) (mac (owner x)) (OwnedStages.diagonalSide n) r m gs u mu →
    ∃ v : CheckAddresses, CheckWords blocks b h K s v (pub (owner x)) decl x x u mu

variable {owner : Fin d → Team} {pub : Team → Arg → Word w} {mac : Team → TeamOpcode.Macros w 8}
    {decl : LengthDeclaration n d} {raw : Symbols d → List Bool}

/-- The square scan actually entered the lower owner's strict role for every increasing
symbol pair. Inverting the role sequence extracts the scatter's real chronological prefix. -/
theorem DispatchScans.strict_visit (scans : DispatchScans owner pub mac n b h K s) (p : Symbols d) :
    let team := owner p.val.1
    let q := (finProdFinEquiv p.val).val
    ∃ r m es u mu, scans.resident team q (r 7) m ∧ ReadyRow (scans.scanLayout team) (readings m) q (.ofWords r m) ∧
      Runs (pub team) (mac team) (OwnedStages.strictSide n b h K s) r m es u mu := by
  intro team q
  obtain ⟨r,m,_,_,_,_,start,returned⟩ := scans.history team
  have inRange : q < (scans.scanLayout team).d*(scans.scanLayout team).d := by
    rw [scans.dimension]; exact (finProdFinEquiv p.val).isLt
  obtain ⟨v,mv,_,y,my,reachable,ready,visit⟩ := returned.visit_at (scans.resident team) start
    (fun range hm h v => scans.advance team range hm h v) q (Nat.zero_le _) inRange
  have left : q/(scans.scanLayout team).d = p.val.1.val := by
    rw [scans.dimension]; exact congrArg (fun a : Fin d × Fin d => a.1.val) (finProdFinEquiv.symm_apply_apply p.val)
  have right : q%(scans.scanLayout team).d = p.val.2.val := by
    rw [scans.dimension]; exact congrArg (fun a : Fin d × Fin d => a.2.val) (finProdFinEquiv.symm_apply_apply p.val)
  have owns := scans.owns p.val.1 p.val.2 mv reachable
  cases visit with
  | skip miss => exact (miss (left ▸ owns)).elim
  | onDiagonal _ same => exact ((ne_of_lt p.property) (Fin.ext (left.symm.trans (same.trans right)))).elim
  | offDiagonal _ _ run =>
    obtain ⟨es,u,mu,_,_,scatter,_⟩ := seq_split run
    exact ⟨v,mv,es,u,mu,reachable,ready,scatter⟩

/-- Native lower-owner returns give one unique global selector function. Its row prefixes
agree with the delivered words, and its values inhabit all the reached physical checker
banks, including after both singleton orientations and the vertex-directory stage. -/
theorem RawScans.recover (scans : RawScans owner pub mac decl raw blocks b h K s) :
    ∃! u : Packet n d blocks → Selector n K h,
      (∀ p : Symbols d, raw p = commonSelectors u decl.1 p) ∧ Nonempty (CheckedScans owner pub mac decl u b s) := by
  have valid (p : Symbols d) : (decodeSelectors n K h (packetVisits blocks decl.1 p).length (raw p)).isSome := by
    obtain ⟨_,_,_,_,_,resident,ready,run⟩ := scans.toDispatchScans.strict_visit p
    obtain ⟨_,_,localSelect,he,_⟩ := scans.strict p resident ready run
    rw [he,commonSelectors_decode]
    rfl
  obtain ⟨u,words,unique⟩ := (validPrefixes_iff_existsUnique decl.1 raw).mp valid
  refine ⟨u,⟨words,⟨{ toDispatchScans := scans.toDispatchScans, strict := ?_, diagonal := scans.diagonal }⟩⟩,
    fun v hv => unique v hv.1⟩
  intro p r m gs y my resident ready run
  obtain ⟨v,data,localSelect,he,stored⟩ := scans.strict p resident ready run
  exact ⟨v,data,fun z => equal_selectors_at (he.symm.trans (words p)) z.val z.property ▸ stored z⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
