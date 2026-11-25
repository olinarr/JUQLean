import Mathlib

/-!
# Proofs of the Adams-Thiele JUQ results

The internal election model and characterization are followed by the bridge to
`Interface.lean`. All finite and infinite cases use the same fixed weight sequence.
-/

namespace JUQLean.Internal

section

/-! Finite approval elections, explicitly relabelled to the finite-type interface. -/

/-- An approval profile together with an admissible positive target size. -/
structure Election (V C : Type*) [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (k : ℕ) where
  approves : V → Finset C
  k_pos : 0 < k
  k_le_m : k ≤ Fintype.card C

namespace Election

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

@[simp] def voters (_E : Election V C k) : Finset V := Finset.univ

@[simp] def candidates (_E : Election V C k) : Finset C := Finset.univ

/-- The number of selected candidates approved by a voter. -/
def utility (E : Election V C k) (W : Finset C) (i : V) : ℕ :=
  (W ∩ E.approves i).card

/-- All voters approving a candidate. -/
def supporters (E : Election V C k) (c : C) : Finset V :=
  E.voters.filter (fun i => c ∈ E.approves i)

/-- Internal rule functions; source-facing validity is supplied by `VotingRule`. -/
structure RawRule (V C : Type*) [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (k : ℕ) where
  apply : Election V C k → Finset (Finset C)

instance : CoeFun (RawRule V C k) (fun _ => Election V C k → Finset (Finset C)) where
  coe F := F.apply

/-- Exhaustive rules return a nonempty collection of size-`k` committees. -/
def RawRule.IsWellFormed (F : RawRule V C k) : Prop :=
  ∀ E, (F E).Nonempty ∧ ∀ W ∈ F E, W.card = k ∧ W ⊆ E.candidates

end Election

end

section

/-! Rational quotas, swaps, and justified upper quota. -/

open Finset

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- The quota uses the target size, including for committees smaller than `k`. -/
def quota (_E : Election V C k) (S : Finset V) : ℚ :=
  (k : ℚ) * S.card / Fintype.card V

/-- The least natural number at least the group's quota. -/
def upperQuota (E : Election V C k) (S : Finset V) : ℕ :=
  ⌈quota E S⌉₊

/-- Replace a selected candidate `c` by an unselected candidate `d`. -/
def swap (W : Finset C) (c d : C) : Finset C := (W ∪ {d}) \ {c}

/-- A pair and a nonempty group witnessing failure of thesis Definition 3.9. -/
def JUQViolation (E : Election V C k) (W : Finset C)
    (c d : C) (S : Finset V) : Prop :=
  c ∈ W ∧ d ∉ W ∧ S.Nonempty ∧ S ⊆ E.supporters d ∧
    (∀ i ∈ E.supporters c, upperQuota E (E.supporters c) < E.utility W i) ∧
    (∀ i ∈ S, E.utility (swap W c d) i ≤ upperQuota E S)

/-- Justified upper quota: no selected candidate can be justifiably replaced. -/
def SatisfiesJUQ (E : Election V C k) (W : Finset C) : Prop :=
  ∀ c d S, ¬ JUQViolation E W c d S

/-- Low-level subset relation for raw local rule functions.
Use `Refines` below to compare valid rules on a source domain. -/
def RawRefines (F G : Election.RawRule V C k) : Prop :=
  ∀ E, F E ⊆ G E

/-- Low-level outcome property for raw local functions, without domain restrictions.
Use `RuleSatisfies` below for valid source rules. -/
def RawRuleSatisfies (F : Election.RawRule V C k)
    (P : Election V C k → Finset C → Prop) : Prop :=
  ∀ E W, W ∈ F E → P E W

theorem rawRuleSatisfies_of_rawRefines {F G : Election.RawRule V C k}
    {P : Election V C k → Finset C → Prop}
    (hFG : RawRefines F G) (hG : RawRuleSatisfies G P) : RawRuleSatisfies F P := by
  intro E W hW
  exact hG E W (hFG E hW)

theorem quota_nonneg (E : Election V C k) (S : Finset V) : 0 ≤ quota E S := by
  unfold quota
  positivity

theorem quota_mono (E : Election V C k) {S T : Finset V} (h : S ⊆ T) :
    quota E S ≤ quota E T := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card h) (by positivity))
    (by positivity)

theorem upperQuota_mono (E : Election V C k) {S T : Finset V} (h : S ⊆ T) :
    upperQuota E S ≤ upperQuota E T := Nat.ceil_mono (quota_mono E h)

@[simp] theorem mem_supporters (E : Election V C k) (c : C) (i : V) :
    i ∈ E.supporters c ↔ c ∈ E.approves i := by
  simp [Election.supporters]

end

section

/-! Thiele scores and finite or infinite composition; the unused zeroth weight is one. -/

open Finset BigOperators

/-- Nonnegative, decreasing marginal weights, normalized at the first seat. -/
structure Weight where
  value : ℕ → ℝ
  zero_eq : value 0 = 1
  first_eq : value 1 = 1
  nonneg : ∀ n, 0 ≤ value n
  decreasing : Antitone value

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- A voter's cumulative score for `t` approved committee members. -/
def voterScore (w : Weight) (t : ℕ) : ℝ :=
  ∑ j ∈ range t, w.value (j + 1)

/-- The sum of voters' Thiele scores. -/
def thieleScore (w : Weight) (E : Election V C k) (W : Finset C) : ℝ :=
  ∑ i : V, voterScore w (E.utility W i)

/-- Keep every maximizer, preserving all ties. -/
noncomputable def selectMax {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) : Finset α := by
  classical
  exact s.filter (fun x => ∀ y ∈ s, f y ≤ f x)

@[simp] theorem mem_selectMax {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ℝ} {x : α} :
    x ∈ selectMax s f ↔ x ∈ s ∧ ∀ y ∈ s, f y ≤ f x := by
  classical
  simp [selectMax]

theorem selectMax_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) : selectMax s f ⊆ s := by
  intro x hx
  exact (mem_selectMax.mp hx).1

theorem selectMax_nonempty {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) (f : α → ℝ) : (selectMax s f).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := s.exists_max_image f hs
  exact ⟨x, mem_selectMax.mpr ⟨hx, hmax⟩⟩

/-- Exhaustive committees, using local's finite candidate set. -/
def feasible (E : Election V C k) : Finset (Finset C) :=
  E.candidates.powersetCard k

@[simp] theorem mem_feasible (E : Election V C k) (W : Finset C) :
    W ∈ feasible E ↔ W.card = k := by simp [feasible]

theorem feasible_nonempty (E : Election V C k) : (feasible E).Nonempty := by
  apply powersetCard_nonempty.mpr
  simpa using E.k_le_m

/-- The ordinary Thiele rule corresponding to a marginal weight function. -/
noncomputable def thieleRule (w : Weight) : Election.RawRule V C k where
  apply E := selectMax (feasible E) (thieleScore w E)

theorem thieleRule_wellFormed (w : Weight) :
    (thieleRule w : Election.RawRule V C k).IsWellFormed := by
  intro E
  refine ⟨selectMax_nonempty (feasible_nonempty E) _, ?_⟩
  intro W hW
  exact ⟨(mem_feasible E W).mp (mem_selectMax.mp hW).1, by simp⟩

/-- A source-level composite sequence is either finite and nonempty or infinite.
There are no empty sequences, optional weights, or gaps. -/
inductive CompositeWeights where
  | finite (first : Weight) (rest : List Weight)
  | infinite (weights : ℕ → Weight)

/-- Build a finite sequence with an explicitly required first weight. -/
def finiteWeights (first : Weight) (rest : List Weight) : CompositeWeights :=
  .finite first rest

/-- Build an infinite sequence. -/
def infiniteWeights (ws : ℕ → Weight) : CompositeWeights := .infinite ws

/-- Apply the specified weight, or stop after the last weight of a finite sequence. -/
noncomputable def applyStage (ws : CompositeWeights) (E : Election V C k)
    (n : ℕ) (s : Finset (Finset C)) : Finset (Finset C) :=
  match ws with
  | .finite first rest =>
    if h : n < (first :: rest).length then
      selectMax s (thieleScore ((first :: rest)[n]'h) E)
    else s
  | .infinite weights => selectMax s (thieleScore (weights n) E)

theorem applyStage_subset (ws : CompositeWeights) (E : Election V C k)
    (n : ℕ) (s : Finset (Finset C)) : applyStage ws E n s ⊆ s := by
  cases ws with
  | finite first rest =>
    simp only [applyStage]
    split_ifs
    · exact selectMax_subset _ _
    · exact Subset.rfl
  | infinite weights => exact selectMax_subset _ _

theorem applyStage_nonempty (ws : CompositeWeights) (E : Election V C k)
    (n : ℕ) {s : Finset (Finset C)} (hs : s.Nonempty) :
    (applyStage ws E n s).Nonempty := by
  cases ws with
  | finite first rest =>
    simp only [applyStage]
    split_ifs
    · exact selectMax_nonempty hs _
    · exact hs
  | infinite weights => exact selectMax_nonempty hs _

/-- Stage zero is the feasible set; subsequent stages apply the listed weights. -/
noncomputable def thieleStage (ws : CompositeWeights) (E : Election V C k) :
    ℕ → Finset (Finset C)
  | 0 => feasible E
  | n + 1 => applyStage ws E n (thieleStage ws E n)

theorem thieleStage_succ_subset (ws : CompositeWeights) (E : Election V C k) (n : ℕ) :
    thieleStage ws E (n + 1) ⊆ thieleStage ws E n := applyStage_subset _ _ _ _

theorem thieleStage_antitone (ws : CompositeWeights) (E : Election V C k) :
    Antitone (thieleStage ws E) :=
  antitone_nat_of_succ_le (thieleStage_succ_subset ws E)

theorem thieleStage_nonempty (ws : CompositeWeights) (E : Election V C k) (n : ℕ) :
    (thieleStage ws E n).Nonempty := by
  induction n with
  | zero => exact feasible_nonempty E
  | succ n ih => exact applyStage_nonempty _ _ _ ih

/-- The intersection of every stage, expressed as a filter of the finite feasible set. -/
noncomputable def compositeRule (ws : CompositeWeights) : Election.RawRule V C k where
  apply E := by
    classical
    exact (feasible E).filter (fun W => ∀ n, W ∈ thieleStage ws E n)

@[simp] theorem mem_compositeRule (ws : CompositeWeights) (E : Election V C k)
    (W : Finset C) : W ∈ compositeRule ws E ↔ ∀ n, W ∈ thieleStage ws E n := by
  classical
  simp only [compositeRule, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h 0, h⟩⟩

/-- Finitely many committees imply that even infinite compositions stabilize. -/
theorem thieleStage_stabilizes (ws : CompositeWeights) (E : Election V C k) :
    ∃ n, ∀ m, n ≤ m → thieleStage ws E m = thieleStage ws E n := by
  classical
  have hex : ∃ a, ∃ n, (thieleStage ws E n).card = a := ⟨_, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  refine ⟨n, fun m hnm => ?_⟩
  apply Finset.eq_of_subset_of_card_le (thieleStage_antitone ws E hnm)
  rw [hn]
  exact Nat.find_min' hex ⟨m, rfl⟩

theorem compositeRule_wellFormed (ws : CompositeWeights) :
    (compositeRule ws : Election.RawRule V C k).IsWellFormed := by
  intro E
  obtain ⟨n, hn⟩ := thieleStage_stabilizes ws E
  obtain ⟨W, hW⟩ := thieleStage_nonempty ws E n
  have hall : ∀ m, W ∈ thieleStage ws E m := by
    intro m
    by_cases h : m ≤ n
    · exact thieleStage_antitone ws E h hW
    · rw [hn m (by omega)]
      exact hW
  refine ⟨⟨W, (mem_compositeRule ws E W).mpr hall⟩, ?_⟩
  intro U hU
  exact ⟨(mem_feasible E U).mp ((mem_compositeRule ws E U).mp hU 0), by simp⟩

/-- A finite composition has no effect after its final listed weight. -/
theorem thieleStage_finite_stable (first : Weight) (rest : List Weight)
    (E : Election V C k) (n : ℕ) :
    thieleStage (finiteWeights first rest) E ((first :: rest).length + n) =
      thieleStage (finiteWeights first rest) E (first :: rest).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, thieleStage]
    simpa only [applyStage, finiteWeights, dif_neg (by omega :
      ¬ (first :: rest).length + n < (first :: rest).length)] using ih

/-- The intersection definition agrees with the last stage for finite lists. -/
theorem mem_compositeRule_finite (first : Weight) (rest : List Weight)
    (E : Election V C k) (W : Finset C) :
    W ∈ compositeRule (finiteWeights first rest) E ↔
      W ∈ thieleStage (finiteWeights first rest) E (first :: rest).length := by
  rw [mem_compositeRule]
  constructor
  · exact fun h => h _
  · intro h n
    by_cases hn : n ≤ (first :: rest).length
    · exact thieleStage_antitone _ E hn h
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (by omega : (first :: rest).length ≤ n)
      simpa only [thieleStage_finite_stable] using h

/-- The first finite stage is exactly the ordinary Thiele rule's winner set. -/
theorem thieleStage_finite_first (first : Weight) (rest : List Weight)
    (E : Election V C k) :
    thieleStage (finiteWeights first rest) E 1 = thieleRule first E := rfl

/-- Infinite sequences apply every weight, with no skipped stages. -/
theorem thieleStage_infinite_succ (ws : ℕ → Weight) (E : Election V C k) (n : ℕ) :
    thieleStage (infiniteWeights ws) E (n + 1) =
      selectMax (thieleStage (infiniteWeights ws) E n) (thieleScore (ws n) E) := rfl

/-- A one-stage composite agrees with the corresponding ordinary Thiele rule. -/
theorem mem_compositeRule_singleton (w : Weight) (E : Election V C k) (W : Finset C) :
    W ∈ compositeRule (finiteWeights w []) E ↔ W ∈ thieleRule w E := by
  rw [mem_compositeRule_finite]
  rfl

end

section

/-! Adams-Thiele: coverage first, then marginal weights (1, 1, 1/2, ...). -/

/-- Chamberlin–Courant: only the first approved representative counts. -/
def ccWeight : Weight where
  value n := if n ≤ 1 then 1 else 0
  zero_eq := by norm_num
  first_eq := by norm_num
  nonneg n := by split_ifs <;> norm_num
  decreasing := by
    intro a b hab
    dsimp
    split_ifs <;> norm_num
    omega

/-- The secondary Adams-Thiele weights, with positive indices `(1,1,1/2,…)`. -/
noncomputable def adamsWeight : Weight where
  value n := 1 / max 1 ((n : ℝ) - 1)
  zero_eq := by norm_num
  first_eq := by norm_num
  nonneg n := by positivity
  decreasing := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · apply max_le_max le_rfl
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith

@[simp] theorem adamsWeight_value (n : ℕ) (hn : 2 ≤ n) :
    adamsWeight.value n = 1 / ((n : ℝ) - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (1 : ℝ) ≤ n - 1 := by linarith
  exact congrArg (fun x : ℝ => 1 / x) (max_eq_right h)

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- Adams-Thiele retains every committee tied on both objectives. -/
noncomputable def adamsThiele : Election.RawRule V C k :=
  compositeRule (finiteWeights ccWeight [adamsWeight])

/-- Membership is exactly primary optimality followed by secondary optimality. -/
theorem mem_adamsThiele (E : Election V C k) (W : Finset C) :
    W ∈ adamsThiele E ↔
      W ∈ selectMax (selectMax (feasible E) (thieleScore ccWeight E))
        (thieleScore adamsWeight E) := by
  rw [adamsThiele, mem_compositeRule_finite]
  rfl

theorem adamsThiele_wellFormed : (adamsThiele : Election.RawRule V C k).IsWellFormed :=
  compositeRule_wellFormed _

theorem adamsThiele_refines_CC :
    RawRefines (adamsThiele : Election.RawRule V C k) (thieleRule ccWeight) := by
  intro E W hW
  exact (mem_selectMax.mp ((mem_adamsThiele E W).mp hW)).1

/-- A lexicographically improving swap excludes a committee from Adams-Thiele. -/
theorem not_mem_adamsThiele_of_improvement (E : Election V C k)
    {W W' : Finset C} (hW' : W'.card = k)
    (hbetter : thieleScore ccWeight E W < thieleScore ccWeight E W' ∨
      (thieleScore ccWeight E W = thieleScore ccWeight E W' ∧
        thieleScore adamsWeight E W < thieleScore adamsWeight E W')) :
    W ∉ adamsThiele E := by
  intro hW
  obtain ⟨hprimary, hsecondary⟩ := mem_selectMax.mp ((mem_adamsThiele E W).mp hW)
  obtain ⟨hfeas, hmax⟩ := mem_selectMax.mp hprimary
  have hW'feas := (mem_feasible E W').mpr hW'
  rcases hbetter with h | ⟨heq, h⟩
  · exact (not_lt_of_ge (hmax W' hW'feas)) h
  · have hW'primary : W' ∈ selectMax (feasible E) (thieleScore ccWeight E) := by
      apply mem_selectMax.mpr
      exact ⟨hW'feas, fun U hU => (hmax U hU).trans_eq heq⟩
    exact (not_lt_of_ge (hsecondary W' hW'primary)) h

end

section

/-! A JUQ violation supplies a feasible swap improving the Adams-Thiele objectives. -/

open Finset BigOperators

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

theorem voterScore_succ (w : Weight) (n : ℕ) :
    voterScore w (n + 1) = voterScore w n + w.value (n + 1) := by simp [voterScore, sum_range_succ]

@[simp] theorem voterScore_cc_zero : voterScore ccWeight 0 = 0 := by simp [voterScore]

@[simp] theorem voterScore_cc_succ (n : ℕ) : voterScore ccWeight (n + 1) = 1 := by
  induction n with
  | zero => simp [voterScore, ccWeight]
  | succ n ih =>
    rw [voterScore_succ, ih]
    simp [ccWeight]

/-- The primary Adams-Thiele objective counts represented voters. -/
theorem voterScore_cc (n : ℕ) :
    voterScore ccWeight n = if n = 0 then 0 else 1 := by cases n <;> simp

theorem quota_pos (E : Election V C k) [Nonempty V]
    {S : Finset V} (hS : S.Nonempty) : 0 < quota E S := by
  have hS' : (0 : ℚ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hk : (0 : ℚ) < k := by exact_mod_cast E.k_pos
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  exact div_pos (mul_pos hk hS') hn

omit [Fintype C] in
/-- Swapping distinct selected/unselected candidates preserves committee size. -/
theorem card_swap {W : Finset C} {c d : C} (hc : c ∈ W) (hd : d ∉ W) :
    (swap W c d).card = W.card := by
  have hcd : c ≠ d := fun h => hd (h ▸ hc)
  have heq : swap W c d = insert d (W.erase c) := by
    ext x
    simp only [swap, mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    grind
  rw [heq, card_insert_of_notMem (by simp [hd]), card_erase_of_mem hc]
  have hp := card_pos.mpr ⟨c, hc⟩
  omega

/-- Utility changes by precisely the two candidates' approval indicators. -/
theorem utility_swap_balance (E : Election V C k) {W : Finset C}
    {c d : C} (hc : c ∈ W) (hd : d ∉ W) (i : V) :
    E.utility (swap W c d) i + (if c ∈ E.approves i then 1 else 0) =
      E.utility W i + (if d ∈ E.approves i then 1 else 0) := by
  have hcd : c ≠ d := fun h => hd (h ▸ hc)
  have heq : swap W c d ∩ E.approves i =
      if d ∈ E.approves i then insert d ((W ∩ E.approves i).erase c)
      else (W ∩ E.approves i).erase c := by
    ext x
    by_cases hda : d ∈ E.approves i
    · simp only [hda, ite_true, swap, mem_inter, mem_sdiff, mem_union,
        mem_singleton, mem_insert, mem_erase]
      grind
    · simp only [hda, ite_false, swap, mem_inter, mem_sdiff, mem_union,
        mem_singleton, mem_erase]
      grind
  unfold Election.utility
  rw [heq]
  have hdn : d ∉ (W ∩ E.approves i).erase c := by simp [hd]
  by_cases hca : c ∈ E.approves i
  · have hcm : c ∈ W ∩ E.approves i := mem_inter.mpr ⟨hc, hca⟩
    have hp := card_pos.mpr ⟨c, hcm⟩
    by_cases hda : d ∈ E.approves i <;>
      simp [hda, hca, hdn, card_erase_of_mem hcm] <;> omega
  · by_cases hda : d ∈ E.approves i <;> simp [hda, hca, hd]

/-- No voter approving the removed candidate can lose her last representative. -/
theorem violation_removed_utility_ge_two (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    {i : V} (hi : c ∈ E.approves i) : 2 ≤ E.utility W i := by
  have him : i ∈ E.supporters c := (mem_supporters E c i).mpr hi
  have hq := quota_pos E ⟨i, him⟩
  have hup : 0 < upperQuota E (E.supporters c) := Nat.ceil_pos.mpr hq
  have hbad := hv.2.2.2.2.1 i him
  omega

/-- Every JUQ swap weakly improves the first Adams-Thiele objective. -/
theorem violation_voter_primary_nondecreasing (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S) (i : V) :
    voterScore ccWeight (E.utility W i) ≤
      voterScore ccWeight (E.utility (swap W c d) i) := by
  rw [voterScore_cc, voterScore_cc]
  have hb := utility_swap_balance E hv.1 hv.2.1 i
  by_cases hold : E.utility W i = 0
  · simp only [hold, ite_true]
    split_ifs <;> norm_num
  · have hnew : E.utility (swap W c d) i ≠ 0 := by
      by_cases hca : c ∈ E.approves i
      · have htwo := violation_removed_utility_ge_two E hv hca
        split_ifs at hb <;> omega
      · simp only [hca, ite_false, add_zero] at hb
        split_ifs at hb <;> omega
    simp [hold, hnew]

/-- Every JUQ swap weakly improves the primary total score. -/
theorem violation_primary_nondecreasing (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S) :
    thieleScore ccWeight E W ≤ thieleScore ccWeight E (swap W c d) :=
  sum_le_sum (fun i _ => violation_voter_primary_nondecreasing E hv i)

/-- If an unrepresented voter approves the incoming candidate, coverage strictly increases. -/
theorem violation_primary_increases (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    {i : V} (hi : d ∈ E.approves i) (hzero : E.utility W i = 0) :
    thieleScore ccWeight E W < thieleScore ccWeight E (swap W c d) := by
  apply sum_lt_sum (fun j _ => violation_voter_primary_nondecreasing E hv j)
  refine ⟨i, mem_univ i, ?_⟩
  have hc : c ∉ E.approves i := by
    intro hc
    have := violation_removed_utility_ge_two E hv hc
    omega
  have hb := utility_swap_balance E hv.1 hv.2.1 i
  simp only [hc, hi, ite_true, ite_false, add_zero, hzero, zero_add] at hb
  simp [hzero, hb]

/-- The beneficiary group must include someone not approving the removed candidate. -/
theorem violation_group_not_subset (E : Election V C k)
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S) :
    ¬ S ⊆ E.supporters c := by
  intro hsub
  obtain ⟨i, hi⟩ := hv.2.2.1
  have hic := hsub hi
  have hid := hv.2.2.2.1 hi
  have hb := utility_swap_balance E hv.1 hv.2.1 i
  have hca := (mem_supporters E c i).mp hic
  have hda := (mem_supporters E d i).mp hid
  simp only [hca, hda, ite_true] at hb
  have hbad := hv.2.2.2.2.1 i hic
  have hgood := hv.2.2.2.2.2 i hi
  have hmono := upperQuota_mono E hsub
  omega

/-- If the two witness groups overlap, the beneficiary group has larger upper quota. -/
theorem violation_overlap_upperQuota (E : Election V C k)
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    {i : V} (hi : i ∈ S) (hc : i ∈ E.supporters c) :
    upperQuota E (E.supporters c) < upperQuota E S := by
  have hid := hv.2.2.2.1 hi
  have hb := utility_swap_balance E hv.1 hv.2.1 i
  have hca := (mem_supporters E c i).mp hc
  have hda := (mem_supporters E d i).mp hid
  simp only [hca, hda, ite_true] at hb
  have hbad := hv.2.2.2.2.1 i hc
  have hgood := hv.2.2.2.2.2 i hi
  omega

/-- If coverage does not increase, the beneficiary group's upper quota is at least two. -/
theorem violation_beneficiary_upperQuota_ge_two (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    (heq : thieleScore ccWeight E W = thieleScore ccWeight E (swap W c d)) :
    2 ≤ upperQuota E S := by
  obtain ⟨i, hi, hc⟩ : ∃ i ∈ S, i ∉ E.supporters c := by
    simpa only [Finset.subset_iff, not_forall, exists_prop] using violation_group_not_subset E hv
  have hca : c ∉ E.approves i := fun h => hc ((mem_supporters E c i).mpr h)
  have hda := (mem_supporters E d i).mp (hv.2.2.2.1 hi)
  have hpos : E.utility W i ≠ 0 := by
    intro hzero
    have hlt := violation_primary_increases E hv hda hzero
    rw [heq] at hlt
    exact (lt_irrefl _) hlt
  have hb := utility_swap_balance E hv.1 hv.2.1 i
  simp only [hca, hda, ite_true, ite_false, add_zero] at hb
  have hgood := hv.2.2.2.2.2 i hi
  omega

end

section

/-! Party-list profiles. Candidate support is explicit in the apportionment domain. -/

open Finset BigOperators

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- Distinct voters approve identical or disjoint ballots, each of size `k`. -/
def HasPartyListBallots (E : Election V C k) : Prop :=
  (∀ i j, E.approves i = E.approves j ∨ Disjoint (E.approves i) (E.approves j)) ∧
  ∀ i, (E.approves i).card = k

/-- Every candidate is approved by at least one voter. -/
def AllCandidatesSupported (E : Election V C k) : Prop :=
  ∀ c, (E.supporters c).Nonempty

/-- The working apportionment domain: party-list ballots and no unsupported
candidates. The extra condition is explicit pending review of the thesis statement. -/
def IsApportionment (E : Election V C k) : Prop :=
  HasPartyListBallots E ∧ AllCandidatesSupported E

/-- The distinct ballots are the candidate sets of the parties. -/
def parties (E : Election V C k) : Finset (Finset C) :=
  univ.image E.approves

/-- Voters belonging to the party with candidate set `B`. -/
def partyVoters (E : Election V C k) (B : Finset C) : Finset V :=
  univ.filter (fun i => E.approves i = B)

/-- AUQ bounds each party's seats by the ceiling of its quota. -/
def SatisfiesAUQ (E : Election V C k) (W : Finset C) : Prop :=
  ∀ B ∈ parties E, (W ∩ B).card ≤ upperQuota E (partyVoters E B)

/-- Only candidates approved by at least one voter may be selected. -/
def SupportedCommittee (E : Election V C k) (W : Finset C) : Prop :=
  ∀ c ∈ W, (E.supporters c).Nonempty

theorem party_nonempty (E : Election V C k) {B : Finset C}
    (hB : B ∈ parties E) : (partyVoters E B).Nonempty := by
  obtain ⟨i, _, hi⟩ := mem_image.mp hB
  exact ⟨i, by simp [partyVoters, hi]⟩

theorem party_card (E : Election V C k) (hE : HasPartyListBallots E)
    {B : Finset C} (hB : B ∈ parties E) : B.card = k := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hB
  exact hE.2 i

theorem parties_disjoint (E : Election V C k) (hE : HasPartyListBallots E) :
    (parties E : Set (Finset C)).PairwiseDisjoint id := by
  intro B hB D hD hBD
  obtain ⟨i, _, rfl⟩ := mem_image.mp hB
  obtain ⟨j, _, rfl⟩ := mem_image.mp hD
  exact (hE.1 i j).resolve_left hBD

theorem supporters_eq_party (E : Election V C k) (hE : HasPartyListBallots E)
    {B : Finset C} (hB : B ∈ parties E) {c : C} (hc : c ∈ B) :
    E.supporters c = partyVoters E B := by
  obtain ⟨j, _, rfl⟩ := mem_image.mp hB
  ext i
  simp only [mem_supporters, partyVoters, mem_filter, mem_univ, true_and]
  constructor
  · intro hi
    rcases hE.1 i j with hij | hij
    · exact hij
    · exact False.elim (Finset.disjoint_left.mp hij hi hc)
  · intro hij
    simpa [hij] using hc

theorem sum_party_sizes (E : Election V C k) :
    ∑ B ∈ parties E, (partyVoters E B).card = Fintype.card V := by
  simpa [parties, partyVoters] using
    (Finset.card_eq_sum_card_image E.approves (univ : Finset V)).symm

theorem sum_party_quotas (E : Election V C k) [Nonempty V] :
    ∑ B ∈ parties E, quota E (partyVoters E B) = (k : ℚ) := by
  simp only [quota, ← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, sum_party_sizes]
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem sum_party_seats_le (E : Election V C k) (hE : HasPartyListBallots E)
    (W : Finset C) : ∑ B ∈ parties E, (W ∩ B).card ≤ W.card := by
  have hd : (parties E : Set (Finset C)).PairwiseDisjoint (fun B => W ∩ B) := by
    intro B hB D hD hBD
    exact (parties_disjoint E hE hB hD hBD).mono inter_subset_right inter_subset_right
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨B, _, hc⟩ := mem_biUnion.mp hc
  exact (mem_inter.mp hc).1

/-- If one party is over quota, some party is strictly below its (unrounded) quota. -/
theorem exists_underrepresented_party (E : Election V C k) [Nonempty V]
    (hE : HasPartyListBallots E) {W : Finset C} (hW : W.card ≤ k)
    {B : Finset C} (hB : B ∈ parties E)
    (hover : upperQuota E (partyVoters E B) < (W ∩ B).card) :
    ∃ D ∈ parties E, ((W ∩ D).card : ℚ) < quota E (partyVoters E D) := by
  by_contra! h
  have hstrict : quota E (partyVoters E B) < ((W ∩ B).card : ℚ) := by
    have hc := Nat.le_ceil (quota E (partyVoters E B))
    have ht : (upperQuota E (partyVoters E B) : ℚ) < (W ∩ B).card := by
      exact_mod_cast hover
    exact hc.trans_lt ht
  have hs := Finset.sum_lt_sum h ⟨B, hB, hstrict⟩
  rw [sum_party_quotas] at hs
  have hle : (∑ D ∈ parties E, ((W ∩ D).card : ℚ)) ≤ k := by
    exact_mod_cast (sum_party_seats_le E hE W).trans hW
  exact (not_lt_of_ge hle) hs

/-- A party member's utility is precisely the number of that party's seats. -/
theorem utility_eq_party_seats (E : Election V C k) {B W : Finset C}
    {i : V} (hi : i ∈ partyVoters E B) : E.utility W i = (W ∩ B).card := by
  have heq : E.approves i = B := (mem_filter.mp hi).2
  simp [Election.utility, heq]

/-- Replacing a candidate outside a party by a new candidate of that party adds one seat. -/
theorem utility_swap_party (E : Election V C k) {B W : Finset C}
    {c d : C} (hc : c ∉ B) (hd : d ∈ B) (hdW : d ∉ W)
    {i : V} (hi : i ∈ partyVoters E B) :
    E.utility (swap W c d) i = (W ∩ B).card + 1 := by
  rw [utility_eq_party_seats E hi]
  have heq : swap W c d ∩ B = insert d (W ∩ B) := by
    ext x
    simp only [swap, mem_inter, mem_sdiff, mem_union, mem_singleton, mem_insert]
    constructor
    · rintro ⟨⟨hx | rfl, hxc⟩, hxB⟩
      · exact Or.inr ⟨hx, hxB⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx, hxB⟩)
      · exact ⟨⟨Or.inr rfl, fun h => hc (h ▸ hd)⟩, hd⟩
      · exact ⟨⟨Or.inl hx, fun h => hc (h ▸ hxB)⟩, hxB⟩
  rw [heq, card_insert_of_notMem (by simp [hdW])]

/-- The easy direction needs support of selected candidates, but no size bound. -/
theorem juq_of_auq (E : Election V C k) (hE : HasPartyListBallots E)
    {W : Finset C} (hW : SupportedCommittee E W) (hAUQ : SatisfiesAUQ E W) :
    SatisfiesJUQ E W := by
  intro c d S hv
  obtain ⟨hcW, _, _, _, hover, _⟩ := hv
  obtain ⟨i, hi⟩ := hW c hcW
  have hc : c ∈ E.approves i := (mem_supporters E c i).mp hi
  have hB : E.approves i ∈ parties E := mem_image.mpr ⟨i, mem_univ i, rfl⟩
  have heq := supporters_eq_party E hE hB hc
  have hbound := hAUQ (E.approves i) hB
  have hbad := hover i hi
  simp only [heq, Election.utility] at hbad
  exact (not_lt_of_ge hbound) hbad

/-- On party-list profiles a JUQ committee obeys AUQ, even with unused candidates. -/
theorem auq_of_juq (E : Election V C k) [Nonempty V] (hE : HasPartyListBallots E)
    {W : Finset C} (hW : W.card ≤ k) (hJUQ : SatisfiesJUQ E W) :
    SatisfiesAUQ E W := by
  intro B hB
  by_contra! hover
  obtain ⟨D, hD, hunder⟩ := exists_underrepresented_party E hE hW hB hover
  have hceil : (W ∩ D).card < upperQuota E (partyVoters E D) := Nat.lt_ceil.mpr hunder
  have hBD : B ≠ D := by
    intro heq
    subst D
    omega
  have hdis := parties_disjoint E hE hB hD hBD
  obtain ⟨c, hcW, hcB⟩ : ∃ c, c ∈ W ∧ c ∈ B := by
    have hpos : 0 < (W ∩ B).card := lt_of_le_of_lt (Nat.zero_le _) hover
    obtain ⟨c, hc⟩ := card_pos.mp hpos
    exact ⟨c, (mem_inter.mp hc).1, (mem_inter.mp hc).2⟩
  have hcD : c ∉ D := fun hc => Finset.disjoint_left.mp hdis hcB hc
  have hquota : quota E (partyVoters E D) ≤ (k : ℚ) := by
    have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hn).mpr
    have hs : ((partyVoters E D).card : ℚ) ≤ Fintype.card V := by
      exact_mod_cast card_le_univ (partyVoters E D)
    nlinarith [show (0 : ℚ) ≤ k by positivity]
  have hseat : (W ∩ D).card < k := by exact_mod_cast hunder.trans_le hquota
  obtain ⟨d, hdD, hdW⟩ : ∃ d ∈ D, d ∉ W := by
    by_contra! hsub
    have heq : W ∩ D = D := inter_eq_right.mpr hsub
    rw [heq, party_card E hE hD] at hseat
    exact (lt_irrefl _) hseat
  apply hJUQ c d (partyVoters E D)
  refine ⟨hcW, hdW, party_nonempty E hD, ?_, ?_, ?_⟩
  · rw [supporters_eq_party E hE hD hdD]
  · intro i hi
    have heq := supporters_eq_party E hE hB hcB
    rw [heq] at hi ⊢
    rw [utility_eq_party_seats E hi]
    exact hover
  · intro i hi
    rw [utility_swap_party E hcD hdD hdW hi]
    exact hceil

/-- Thesis Proposition 3.4 with the support hypothesis made explicit. -/
theorem auq_iff_juq_of_supportedCommittee (E : Election V C k) [Nonempty V] (hE : HasPartyListBallots E)
    {W : Finset C} (hW : W.card ≤ k) (hsupport : SupportedCommittee E W) :
    SatisfiesAUQ E W ↔ SatisfiesJUQ E W :=
  ⟨juq_of_auq E hE hsupport, auq_of_juq E hE hW⟩

/-- Thesis Proposition 3.4 on the agreed apportionment domain. -/
theorem auq_iff_juq (E : Election V C k) [Nonempty V]
    (hE : IsApportionment E) {W : Finset C} (hW : W.card ≤ k) :
    SatisfiesAUQ E W ↔ SatisfiesJUQ E W :=
  auq_iff_juq_of_supportedCommittee E hE.1 hW (fun c _ => hE.2 c)

/-- The equivalence lifts to all outcomes of an exhaustive rule on this domain. -/
theorem rule_auq_iff_juq_on_apportionment [Nonempty V]
    (F : Election.RawRule V C k) (hF : F.IsWellFormed) :
    RawRuleSatisfies F (fun E W => IsApportionment E → SatisfiesAUQ E W) ↔
      RawRuleSatisfies F (fun E W => IsApportionment E → SatisfiesJUQ E W) := by
  constructor
  · intro h E W hW hE
    exact (auq_iff_juq E hE (Nat.le_of_eq ((hF E).2 W hW).1)).mp (h E W hW hE)
  · intro h E W hW hE
    exact (auq_iff_juq E hE (Nat.le_of_eq ((hF E).2 W hW).1)).mpr (h E W hW hE)

end

section

/-! Source domains, valid rules, and families with one fixed weight sequence. -/

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- The working general domain: empty ballots and unsupported candidates are allowed. -/
def GeneralProfile (_E : Election V C k) : Prop := 0 < Fintype.card V

/-- Section 2.1 of the EC paper. Empty ballots are permitted. -/
def PaperProfile (E : Election V C k) : Prop :=
  0 < Fintype.card V ∧ AllCandidatesSupported E

/-- The approval-profile domain of the thesis's Preliminaries. -/
def ThesisProfile (E : Election V C k) : Prop :=
  0 < Fintype.card V ∧ ∀ i, (E.approves i).Nonempty

/-- The agreed apportionment domain includes a nonempty electorate. -/
def ApportionmentProfile (E : Election V C k) : Prop :=
  0 < Fintype.card V ∧ IsApportionment E

theorem ApportionmentProfile.general {E : Election V C k}
    (hE : ApportionmentProfile E) : GeneralProfile E := hE.1

theorem ApportionmentProfile.paper {E : Election V C k}
    (hE : ApportionmentProfile E) : PaperProfile E := ⟨hE.1, hE.2.2⟩

theorem ApportionmentProfile.thesis {E : Election V C k}
    (hE : ApportionmentProfile E) : ThesisProfile E := by
  refine ⟨hE.1, fun i => Finset.card_pos.mp ?_⟩
  rw [hE.2.1.2 i]
  exact E.k_pos

/-- A valid source rule, with no assumption of exhaustiveness. The raw function's
values outside `D` have no role in the source-facing properties below. -/
structure VotingRule (D : Election V C k → Prop) where
  toABCRule : Election.RawRule V C k
  valid : ∀ E, D E → (toABCRule E).Nonempty ∧
    ∀ W ∈ toABCRule E, W.card ≤ k

/-- An local exhaustive, well-formed rule is also a valid source rule. -/
def VotingRule.ofWellFormed (D : Election V C k → Prop)
    (F : Election.RawRule V C k) (hF : F.IsWellFormed) : VotingRule D where
  toABCRule := F
  valid E _ := ⟨(hF E).1, fun W hW => Nat.le_of_eq ((hF E).2 W hW).1⟩

/-- Source refinement compares two valid rules on their specified domain. -/
def Refines {D : Election V C k → Prop} (F G : VotingRule D) : Prop :=
  ∀ E, D E → F.toABCRule E ⊆ G.toABCRule E

/-- All returned committees satisfy the property, on admissible profiles. -/
def RuleSatisfies {D : Election V C k → Prop} (F : VotingRule D)
    (P : Election V C k → Finset C → Prop) : Prop :=
  ∀ E, D E → ∀ W ∈ F.toABCRule E, P E W

/-- Exhaustiveness is distinct from validity, as in both sources. -/
def VotingRule.IsExhaustive {D : Election V C k → Prop} (F : VotingRule D) : Prop :=
  ∀ E, D E → ∀ W ∈ F.toABCRule E, W.card = k

theorem RuleSatisfies.of_refines {D : Election V C k → Prop}
    {F G : VotingRule D} {P : Election V C k → Finset C → Prop}
    (hFG : Refines F G) (hG : RuleSatisfies G P) : RuleSatisfies F P := by
  intro E hE W hW
  exact hG E hE W (hFG E hE hW)

/-- A composite rule is valid on either source domain (and even on larger domains). -/
noncomputable def compositeVotingRule (ws : CompositeWeights)
    (D : Election V C k → Prop) : VotingRule D :=
  VotingRule.ofWellFormed D (compositeRule ws) (compositeRule_wellFormed ws)

noncomputable def thieleVotingRule (w : Weight) (D : Election V C k → Prop) : VotingRule D :=
  VotingRule.ofWellFormed D (thieleRule w) (thieleRule_wellFormed w)

noncomputable def adamsVotingRule (D : Election V C k → Prop) : VotingRule D :=
  VotingRule.ofWellFormed D adamsThiele adamsThiele_wellFormed

theorem adamsVotingRule_refines_CC (D : Election V C k → Prop) :
    Refines (adamsVotingRule D) (thieleVotingRule ccWeight D) := by
  intro E _ W hW
  exact adamsThiele_refines_CC E hW

theorem compositeVotingRule_exhaustive (ws : CompositeWeights)
    (D : Election V C k → Prop) : (compositeVotingRule ws D).IsExhaustive := by
  intro E _ W hW
  exact ((compositeRule_wellFormed ws E).2 W hW).1

/-- Proposition 3.4 for valid source rules, including nonexhaustive ones. -/
theorem valid_rule_auq_iff_juq (F : VotingRule (ApportionmentProfile (V := V) (C := C) (k := k))) :
    RuleSatisfies F SatisfiesAUQ ↔ RuleSatisfies F SatisfiesJUQ := by
  have hequiv (E : Election V C k) (hE : ApportionmentProfile E)
      (W : Finset C) (hW : W ∈ F.toABCRule E) :
      SatisfiesAUQ E W ↔ SatisfiesJUQ E W := by
    letI : Nonempty V := Fintype.card_pos_iff.mp hE.1
    exact auq_iff_juq E hE.2 ((F.valid E hE).2 W hW)
  constructor
  · intro h E hE W hW
    exact (hequiv E hE W hW).mp (h E hE W hW)
  · intro h E hE W hW
    exact (hequiv E hE W hW).mpr (h E hE W hW)

/-- A source rule family ranges over arbitrary finite voter and candidate types
and every target size. It is not restricted to one election size or labeling. -/
abbrev VotingRuleFamily
    (domain : {V C : Type} → [Fintype V] → [Fintype C] →
      [DecidableEq V] → [DecidableEq C] → {k : ℕ} → Election V C k → Prop) :=
  (V C : Type) → [Fintype V] → [Fintype C] → [DecidableEq V] → [DecidableEq C] →
    (k : ℕ) → VotingRule (domain (V := V) (C := C) (k := k))

/-- The weight sequence is supplied once, outside all type and size quantifiers. -/
noncomputable def compositeFamily (ws : CompositeWeights) : VotingRuleFamily GeneralProfile := by
  intro V C _ _ _ _ k
  exact compositeVotingRule ws GeneralProfile

noncomputable def adamsFamily : VotingRuleFamily GeneralProfile := by
  intro V C _ _ _ _ k
  exact adamsVotingRule GeneralProfile

/-- Global refinement on the general domain. -/
def FamilyRefines (F G : VotingRuleFamily GeneralProfile) : Prop :=
  ∀ (V C : Type) [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] (k : ℕ),
    Refines (F V C k) (G V C k)

/-- JUQ on every admissible election, of every size. -/
def FamilySatisfiesJUQ (F : VotingRuleFamily GeneralProfile) : Prop :=
  ∀ (V C : Type) [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] (k : ℕ),
    RuleSatisfies (F V C k) SatisfiesJUQ

/-- AUQ is only tested on apportionment elections, across every size. -/
def FamilySatisfiesAUQ (F : VotingRuleFamily GeneralProfile) : Prop :=
  ∀ (V C : Type) [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
    (k : ℕ) (E : Election V C k), ApportionmentProfile E →
    ∀ W ∈ (F V C k).toABCRule E, SatisfiesAUQ E W

/-- The global statement of Theorem 6. Proved below as `upperQuotaCharacterization`. -/
def UpperQuotaCharacterization (ws : CompositeWeights) : Prop :=
  FamilySatisfiesAUQ (compositeFamily ws) ↔ FamilyRefines (compositeFamily ws) adamsFamily

/-- The global JUQ corollary. Proved below as `juqCharacterization`. -/
def JUQCharacterization (ws : CompositeWeights) : Prop :=
  FamilySatisfiesJUQ (compositeFamily ws) ↔ FamilyRefines (compositeFamily ws) adamsFamily

/-- JUQ on all profiles implies AUQ on apportionment profiles. Validity supplies
committee size bounds; the domain hypothesis supplies the nonempty electorate. -/
theorem family_auq_of_juq (F : VotingRuleFamily GeneralProfile)
    (hF : FamilySatisfiesJUQ F) : FamilySatisfiesAUQ F := by
  intro V C _ _ _ _ k E hE W hW
  letI : Nonempty V := Fintype.card_pos_iff.mp hE.1
  apply (auq_iff_juq E hE.2 (((F V C k).valid E hE.general).2 W hW)).mpr
  exact hF V C k E hE.general W hW

theorem FamilySatisfiesJUQ.of_refines {F G : VotingRuleFamily GeneralProfile}
    (hFG : FamilyRefines F G) (hG : FamilySatisfiesJUQ G) : FamilySatisfiesJUQ F := by
  intro V C _ _ _ _ k
  exact RuleSatisfies.of_refines (hFG V C k) (hG V C k)

/-- Logical assembly of the JUQ characterization from the two main results. -/
theorem juqCharacterization_of_upperQuota (ws : CompositeWeights)
    (hUpper : UpperQuotaCharacterization ws) (hAdams : FamilySatisfiesJUQ adamsFamily) :
    JUQCharacterization ws := by
  constructor
  · intro h
    exact hUpper.mp (family_auq_of_juq (compositeFamily ws) h)
  · intro h
    exact FamilySatisfiesJUQ.of_refines h hAdams

end

section

/-! Theorem 3.5: a violation improves coverage or the secondary score. -/

open Finset BigOperators

/-- The numerical inequality underlying the secondary-score improvement. -/
private theorem gain_gt_loss {a b x y r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 < y)
    (hqa : r * x ≤ a) (hqb : b < r * y) : x / a < y / b := by
  apply (div_lt_div_iff₀ ha hb).mpr
  by_cases hzero : x = 0
  · rw [hzero, zero_mul]
    exact mul_pos hy ha
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  have hmul := mul_lt_mul_of_pos_left hqb hpos
  have hmul' := mul_le_mul_of_nonneg_right hqa (le_of_lt hy)
  nlinarith

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

private theorem adams_increment (n : ℕ) (hn : 0 < n) :
    voterScore adamsWeight (n + 1) - voterScore adamsWeight n = 1 / (n : ℝ) := by
  rw [voterScore_succ, add_sub_cancel_left, adamsWeight_value _ (by omega)]
  congr 1
  push_cast
  ring

private theorem adams_increment_nonneg (n : ℕ) :
    0 ≤ voterScore adamsWeight (n + 1) - voterScore adamsWeight n := by
  rw [voterScore_succ, add_sub_cancel_left]
  exact adamsWeight.nonneg _

private theorem covered_incoming (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    (heq : thieleScore ccWeight E W = thieleScore ccWeight E (swap W c d))
    {i : V} (hi : d ∈ E.approves i) : 0 < E.utility W i := by
  by_contra! h
  have hz : E.utility W i = 0 := by omega
  have hlt := violation_primary_increases E hv hi hz
  rw [heq] at hlt
  exact (lt_irrefl _) hlt

/-- A pointwise lower bound allowing a virtual gain and loss for overlapping voters. -/
private theorem voter_delta_lower_bound (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    (heq : thieleScore ccWeight E W = thieleScore ccWeight E (swap W c d))
    {a b : ℝ} (ha : 0 < a) (_hb : 0 < b)
    (hloss : ∀ i, c ∈ E.approves i → a ≤ (E.utility W i : ℝ) - 1)
    (hgain : ∀ i ∈ S, c ∉ E.approves i → (E.utility W i : ℝ) ≤ b)
    (hoverlap : ∀ i ∈ S, c ∈ E.approves i → a ≤ b) (i : V) :
    (if i ∈ S then 1 / b else 0) - (if i ∈ E.supporters c then 1 / a else 0) ≤
      voterScore adamsWeight (E.utility (swap W c d) i) -
        voterScore adamsWeight (E.utility W i) := by
  have hbal := utility_swap_balance E hv.1 hv.2.1 i
  simp only [mem_supporters]
  by_cases hc : c ∈ E.approves i
  · by_cases hd : d ∈ E.approves i
    · have hu : E.utility (swap W c d) i = E.utility W i := by
        simp only [hc, hd, ite_true] at hbal
        omega
      rw [hu, sub_self]
      by_cases hi : i ∈ S
      · simp only [hi, hc, ite_true]
        exact sub_nonpos.mpr (one_div_le_one_div_of_le ha (hoverlap i hi hc))
      · simp [hi, hc, le_of_lt ha]
    · have hi : i ∉ S := fun hi => hd ((mem_supporters E d i).mp (hv.2.2.2.1 hi))
      have htwo := violation_removed_utility_ge_two E hv hc
      have hu : E.utility (swap W c d) i + 1 = E.utility W i := by
        simpa only [hc, hd, ite_true, ite_false, add_zero] using hbal
      have hp : 0 < E.utility (swap W c d) i := by omega
      have hinc := adams_increment (E.utility (swap W c d) i) hp
      have hbound : a ≤ (E.utility (swap W c d) i : ℝ) := by
        have hcast : (E.utility W i : ℝ) = E.utility (swap W c d) i + 1 := by
          exact_mod_cast hu.symm
        linarith [hloss i hc]
      have hinv := one_div_le_one_div_of_le ha hbound
      simp only [hi, hc, ite_false, ite_true, zero_sub]
      rw [hu] at hinc
      linarith
  · by_cases hd : d ∈ E.approves i
    · have hu : E.utility (swap W c d) i = E.utility W i + 1 := by
        simpa only [hc, hd, ite_true, ite_false, add_zero] using hbal
      rw [hu, adams_increment _ (covered_incoming E hv heq hd)]
      by_cases hi : i ∈ S
      · simp only [hi, hc, ite_true, ite_false, sub_zero]
        have hp : (0 : ℝ) < E.utility W i := by
          exact_mod_cast covered_incoming E hv heq hd
        exact one_div_le_one_div_of_le hp (hgain i hi hc)
      · simp only [hi, hc, ite_false, sub_zero]
        positivity
    · have hi : i ∉ S := fun hi => hd ((mem_supporters E d i).mp (hv.2.2.2.1 hi))
      have hu : E.utility (swap W c d) i = E.utility W i := by
        simpa only [hc, hd, ite_false, add_zero] using hbal
      simp [hi, hc, hu]

private theorem real_quota (E : Election V C k) (S : Finset V) :
    (quota E S : ℝ) = (k : ℝ) / Fintype.card V * S.card := by
  unfold quota
  push_cast
  ring

/-- If a JUQ swap leaves coverage unchanged, it strictly increases the secondary score. -/
theorem violation_secondary_increases (E : Election V C k) [Nonempty V]
    {W : Finset C} {c d : C} {S : Finset V} (hv : JUQViolation E W c d S)
    (heq : thieleScore ccWeight E W = thieleScore ccWeight E (swap W c d)) :
    thieleScore adamsWeight E W < thieleScore adamsWeight E (swap W c d) := by
  let A := E.supporters c
  let a : ℝ := max 1 (upperQuota E A : ℝ)
  let b : ℝ := (upperQuota E S : ℝ) - 1
  let r : ℝ := (k : ℝ) / Fintype.card V
  have hbeta := violation_beneficiary_upperQuota_ge_two E hv heq
  have hbeta' : (2 : ℝ) ≤ upperQuota E S := by exact_mod_cast hbeta
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : 1 ≤ b := by dsimp [b]; linarith
  have hloss (i : V) (hi : c ∈ E.approves i) : a ≤ (E.utility W i : ℝ) - 1 := by
    have hic := (mem_supporters E c i).mpr hi
    have hbad := hv.2.2.2.2.1 i hic
    have hbad' : (upperQuota E A : ℝ) + 1 ≤ E.utility W i := by
      exact_mod_cast hbad
    have htwo : (2 : ℝ) ≤ E.utility W i := by
      exact_mod_cast violation_removed_utility_ge_two E hv hi
    exact max_le (by linarith) (by linarith)
  have hgain (i : V) (hi : i ∈ S) (hc : c ∉ E.approves i) : (E.utility W i : ℝ) ≤ b := by
    have hd := (mem_supporters E d i).mp (hv.2.2.2.1 hi)
    have hbal := utility_swap_balance E hv.1 hv.2.1 i
    simp only [hc, hd, ite_true, ite_false, add_zero] at hbal
    have hgood := hv.2.2.2.2.2 i hi
    have hgood' : (E.utility W i : ℝ) + 1 ≤ upperQuota E S := by
      exact_mod_cast (show E.utility W i + 1 ≤ upperQuota E S by omega)
    dsimp [b]
    linarith
  have hoverlap (i : V) (hi : i ∈ S) (hc : c ∈ E.approves i) : a ≤ b := by
    have ht := violation_overlap_upperQuota E hv hi ((mem_supporters E c i).mpr hc)
    have ht' : (upperQuota E A : ℝ) + 1 ≤ upperQuota E S := by exact_mod_cast ht
    apply max_le hb1
    dsimp [b]
    linarith
  have hqa : r * A.card ≤ a := by
    have hq : (quota E A : ℝ) ≤ (upperQuota E A : ℝ) := by
      exact_mod_cast Nat.le_ceil (quota E A)
    rw [real_quota] at hq
    exact hq.trans (le_max_right _ _)
  have hqb : b < r * S.card := by
    have hq : (upperQuota E S : ℝ) < (quota E S : ℝ) + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one (quota_nonneg E S)
    rw [real_quota] at hq
    dsimp [b, r]
    linarith
  have hnum : (A.card : ℝ) / a < (S.card : ℝ) / b :=
    gain_gt_loss ha hb (by positivity) (by exact_mod_cast card_pos.mpr hv.2.2.1) hqa hqb
  have hsum : (S.card : ℝ) / b - (A.card : ℝ) / a ≤
      thieleScore adamsWeight E (swap W c d) - thieleScore adamsWeight E W := by
    have hpoint := Finset.sum_le_sum (s := (univ : Finset V))
      (fun i _ => voter_delta_lower_bound E hv heq ha hb hloss hgain hoverlap i)
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem_eq, Finset.sum_const,
      nsmul_eq_mul, mul_one_div] at hpoint
    simpa only [thieleScore, ← Finset.sum_sub_distrib] using hpoint
  linarith

/-- Thesis Theorem 3.5, without restrictions on ballots or candidate support. -/
theorem adamsThiele_satisfies_juq (E : Election V C k) [Nonempty V]
    {W : Finset C} (hW : W ∈ adamsThiele E) : SatisfiesJUQ E W := by
  intro c d S hv
  have hsize := (adamsThiele_wellFormed E).2 W hW
  have hfeas : (swap W c d).card = k := (card_swap hv.1 hv.2.1).trans hsize.1
  have hprimary := violation_primary_nondecreasing E hv
  apply not_mem_adamsThiele_of_improvement E hfeas ?_ hW
  rcases lt_or_eq_of_le hprimary with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, violation_secondary_increases E hv heq⟩

/-- Theorem 3.5 as a valid-rule statement on the agreed general domain. -/
theorem adamsVotingRule_satisfies_juq :
    RuleSatisfies (adamsVotingRule (GeneralProfile (V := V) (C := C) (k := k))) SatisfiesJUQ := by
  intro E hE W hW
  letI : Nonempty V := Fintype.card_pos_iff.mp hE
  exact adamsThiele_satisfies_juq E hW

/-- Every valid refinement of Adams-Thiele satisfies JUQ on the full general domain. -/
theorem refinement_adams_satisfies_juq
    {F : VotingRule (GeneralProfile (V := V) (C := C) (k := k))}
    (hF : Refines F (adamsVotingRule GeneralProfile)) : RuleSatisfies F SatisfiesJUQ :=
  RuleSatisfies.of_refines hF adamsVotingRule_satisfies_juq

/-- Theorem 3.5 holds uniformly across all finite electorates, agendas, and target sizes. -/
theorem adamsFamily_satisfies_juq : FamilySatisfiesJUQ adamsFamily := by
  intro V C _ _ _ _ k
  exact adamsVotingRule_satisfies_juq

theorem refinement_adamsFamily_satisfies_juq {F : VotingRuleFamily GeneralProfile}
    (hF : FamilyRefines F adamsFamily) : FamilySatisfiesJUQ F :=
  FamilySatisfiesJUQ.of_refines hF adamsFamily_satisfies_juq

/-- The sufficiency direction of Theorem 3.6, using only the supported
apportionment test class. Necessity is proved below as `AUQ_implies_refines_adams`. -/
theorem refinement_adamsFamily_satisfies_auq {F : VotingRuleFamily GeneralProfile}
    (hF : FamilyRefines F adamsFamily) : FamilySatisfiesAUQ F :=
  family_auq_of_juq F (refinement_adamsFamily_satisfies_juq hF)

/-- Logical assembly of both global characterizations from AUQ necessity.
The unconditional results are proved below as `upperQuotaCharacterization` and
`juqCharacterization`. -/
theorem characterizations_of_auq_necessity (ws : CompositeWeights)
    (hnecessary : FamilySatisfiesAUQ (compositeFamily ws) →
      FamilyRefines (compositeFamily ws) adamsFamily) :
    UpperQuotaCharacterization ws ∧ JUQCharacterization ws := by
  have hUpper : UpperQuotaCharacterization ws :=
    ⟨hnecessary, refinement_adamsFamily_satisfies_auq⟩
  exact ⟨hUpper, juqCharacterization_of_upperQuota ws hUpper adamsFamily_satisfies_juq⟩

end

section

/-! Necessary conditions for the characterization and the one-stage CC counterexample. -/

open Finset BigOperators

/-- The first weight is always present, even for infinite compositions. -/
def CompositeWeights.firstWeight : CompositeWeights → Weight
  | .finite first _ => first
  | .infinite weights => weights 0

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- Every final winner maximizes the first score, regardless of later tie-breaking. -/
theorem composite_refines_first (ws : CompositeWeights) :
    RawRefines (compositeRule ws : Election.RawRule V C k)
      (thieleRule ws.firstWeight) := by
  intro E W hW
  have hfirst := (mem_compositeRule ws E W).mp hW 1
  cases ws <;> exact hfirst

/-- A weight vector with second weight zero is exactly CC. -/
theorem weight_eq_cc_of_second_zero (w : Weight) (hzero : w.value 2 = 0) : w = ccWeight := by
  have hfun : w.value = ccWeight.value := by
    funext n
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp [ccWeight, w.zero_eq, w.first_eq]
    · have hge : 2 ≤ n := by omega
      have hle := w.decreasing hge
      rw [hzero] at hle
      have hv : w.value n = 0 := le_antisymm hle (w.nonneg n)
      simp [ccWeight, hn, hv]
  cases w
  simp only [ccWeight, Weight.mk.injEq]
  exact hfun

/-- Coverage never exceeds the electorate size. -/
theorem cc_score_le_voters (E : Election V C k) (W : Finset C) :
    thieleScore ccWeight E W ≤ Fintype.card V := by
  calc
    thieleScore ccWeight E W ≤ ∑ _i : V, (1 : ℝ) := by
      apply sum_le_sum
      intro i _
      rw [voterScore_cc]
      split_ifs <;> norm_num
    _ = _ := by simp

namespace CharacterizationExamples

/-- Two parties of sizes one and two, each with three candidates. -/
def twoPartyInstance : Election (Fin 3) (Fin 6) 3 where
  approves i := if i = 0 then {0, 1, 2} else {3, 4, 5}
  k_pos := by decide
  k_le_m := by decide

theorem twoParty_is_apportionment : ApportionmentProfile twoPartyInstance := by
  unfold ApportionmentProfile IsApportionment HasPartyListBallots AllCandidatesSupported
  decide

/-- CC may award two seats to the one-voter party and one to the two-voter party. -/
theorem bad_committee_wins_CC : ({0, 1, 3} : Finset (Fin 6)) ∈ thieleRule ccWeight twoPartyInstance := by
  apply mem_selectMax.mpr
  constructor
  · rw [mem_feasible]
    decide
  · intro W _
    have hscore : thieleScore ccWeight twoPartyInstance {0, 1, 3} = 3 := by
      norm_num [thieleScore, Fin.sum_univ_succ, twoPartyInstance, Election.utility,
        voterScore_cc]
    rw [hscore]
    simpa using cc_score_le_voters twoPartyInstance W

theorem bad_committee_fails_AUQ : ¬ SatisfiesAUQ twoPartyInstance {0, 1, 3} := by
  intro h
  have hB : ({0, 1, 2} : Finset (Fin 6)) ∈ parties twoPartyInstance :=
    mem_image.mpr ⟨0, mem_univ _, rfl⟩
  have hb := h {0, 1, 2} hB
  have hseats : (({0, 1, 3} : Finset (Fin 6)) ∩ {0, 1, 2}).card = 2 := by decide
  have hparty : partyVoters twoPartyInstance {0, 1, 2} = {0} := by decide
  rw [hseats, hparty] at hb
  norm_num [upperQuota, quota] at hb

theorem bad_committee_fails_JUQ : ¬ SatisfiesJUQ twoPartyInstance {0, 1, 3} := by
  intro h
  exact bad_committee_fails_AUQ ((auq_iff_juq twoPartyInstance
    twoParty_is_apportionment.2 (by decide)).mpr h)

end CharacterizationExamples

/-- A one-stage CC rule fails AUQ on the fully supported apportionment test class. -/
theorem single_CC_fails_global_AUQ :
    ¬ FamilySatisfiesAUQ (compositeFamily (finiteWeights ccWeight [])) := by
  intro h
  apply CharacterizationExamples.bad_committee_fails_AUQ
  apply h (Fin 3) (Fin 6) 3 CharacterizationExamples.twoPartyInstance
    CharacterizationExamples.twoParty_is_apportionment
  exact (mem_compositeRule_singleton _ _ _).mpr CharacterizationExamples.bad_committee_wins_CC

theorem single_CC_fails_global_JUQ :
    ¬ FamilySatisfiesJUQ (compositeFamily (finiteWeights ccWeight [])) := by
  intro h
  exact single_CC_fails_global_AUQ (family_auq_of_juq _ h)

end

section

/-! Realizing integer party-size vectors as elections. -/

open Finset BigOperators

namespace PartyList

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The candidate set belonging to a given party. -/
def ballot (k : ℕ) (p : P) : Finset (P × Fin k) := {p} ×ˢ univ

omit [Fintype P] [DecidableEq P] in
@[simp] theorem mem_ballot {k : ℕ} {p : P} {c : P × Fin k} :
    c ∈ ballot k p ↔ c.1 = p := by
  rcases c with ⟨q, j⟩
  simp [ballot, eq_comm]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem card_ballot (k : ℕ) (p : P) : (ballot k p).card = k := by simp [ballot]

/-- Every party receives a block of `k` candidates. -/
def instanceOf (v : P → ℕ) [Nonempty P] (k : ℕ) (hk : 0 < k) :
    Election (Σ p, Fin (v p)) (P × Fin k) k where
  approves i := ballot k i.1
  k_pos := hk
  k_le_m := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact le_mul_of_one_le_left (Nat.zero_le k) Fintype.card_pos

omit [Fintype P] [DecidableEq P] in
theorem ballot_disjoint {k : ℕ} {p q : P} (hpq : p ≠ q) :
    Disjoint (ballot k p) (ballot k q) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact hpq (((mem_ballot.mp hx).symm).trans (mem_ballot.mp hy))

omit [Fintype P] [DecidableEq P] in
theorem ballot_injective {k : ℕ} (hk : 0 < k) : Function.Injective (ballot (P := P) k) := by
  intro p q heq
  have hm : (p, (⟨0, hk⟩ : Fin k)) ∈ ballot k q := heq ▸ (by simp)
  exact mem_ballot.mp hm

theorem is_apportionment (v : P → ℕ) [Nonempty P] (hv : ∀ p, 0 < v p)
    (k : ℕ) (hk : 0 < k) : ApportionmentProfile (instanceOf v k hk) := by
  have hV : Nonempty (Σ p, Fin (v p)) := by
    obtain ⟨p⟩ := ‹Nonempty P›
    exact ⟨⟨p, ⟨0, hv p⟩⟩⟩
  refine ⟨Fintype.card_pos_iff.mpr hV, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    by_cases h : i.1 = j.1
    · exact Or.inl (congrArg (ballot k) h)
    · exact Or.inr (ballot_disjoint h)
  · intro i
    exact card_ballot k i.1
  · intro c
    refine ⟨⟨c.1, ⟨0, hv c.1⟩⟩, ?_⟩
    rw [mem_supporters]
    simp [instanceOf]

/-- Seats held by a party in a concrete committee. -/
def seats {k : ℕ} (W : Finset (P × Fin k)) (p : P) : ℕ :=
  (W ∩ ballot k p).card

theorem utility_eq_seats (v : P → ℕ) [Nonempty P] (k : ℕ) (hk : 0 < k)
    (W : Finset (P × Fin k)) (i : Σ p, Fin (v p)) :
    (instanceOf v k hk).utility W i = seats W i.1 := rfl

omit [DecidableEq P] in
/-- Voter counts sum to the electorate cardinality. -/
theorem electorate_card (v : P → ℕ) : Fintype.card (Σ p, Fin (v p)) = ∑ p, v p := by simp [Fintype.card_sigma]

/-- The party-list score is the weighted sum of cumulative seat scores. -/
theorem score_eq (v : P → ℕ) [Nonempty P] (k : ℕ) (hk : 0 < k)
    (w : Weight) (W : Finset (P × Fin k)) :
    thieleScore w (instanceOf v k hk) W = ∑ p, (v p : ℝ) * voterScore w (seats W p) := by
  simp [thieleScore, utility_eq_seats, Fintype.sum_sigma]

theorem sum_seats {k : ℕ} (W : Finset (P × Fin k)) : ∑ p, seats W p = W.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := W) (t := univ)
    (fun _ _ => mem_univ _)
  have heq (p : P) : W.filter (fun c => c.1 = p) = W ∩ ballot k p := by
    ext c
    simp
  simpa only [heq, seats] using h.symm

/-- Every nonempty party occurs as an approval ballot. -/
theorem ballot_mem_parties (v : P → ℕ) [Nonempty P] {p : P} (hv : 0 < v p)
    (k : ℕ) (hk : 0 < k) : ballot k p ∈ parties (instanceOf v k hk) :=
  mem_image.mpr ⟨⟨p, ⟨0, hv⟩⟩, mem_univ _, rfl⟩

theorem party_voters_card (v : P → ℕ) [Nonempty P] (p : P) (k : ℕ) (hk : 0 < k) :
    (partyVoters (instanceOf v k hk) (ballot k p)).card = v p := by
  have heq : partyVoters (instanceOf v k hk) (ballot k p) =
      univ.filter (fun i : Σ p, Fin (v p) => i.1 = p) := by
    ext i
    simp only [partyVoters, mem_filter, mem_univ, true_and, instanceOf]
    exact (ballot_injective hk).eq_iff
  rw [heq]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_sigma]
  change (∑ x : P, ∑ _i : Fin (v x), if x = p then (1 : ℕ) else 0) = v p
  have hin (x : P) : (∑ _i : Fin (v x), if x = p then (1 : ℕ) else 0) =
      if x = p then v x else 0 := by
    by_cases h : x = p <;> simp [h]
  simp_rw [hin]
  simp

/-- AUQ in the source model implies the familiar bound on each party's seats. -/
theorem auq_bound (v : P → ℕ) [Nonempty P] (hv : ∀ p, 0 < v p)
    (k : ℕ) (hk : 0 < k) {W : Finset (P × Fin k)}
    (hW : SatisfiesAUQ (instanceOf v k hk) W) (p : P) :
    seats W p ≤ ⌈(k : ℚ) * v p / (∑ q, v q)⌉₊ := by
  have h := hW (ballot k p) (ballot_mem_parties v (hv p) k hk)
  simpa only [upperQuota, quota, electorate_card, party_voters_card, seats] using h

end PartyList

end

section

/-! Two-seat party-list tests force the first weight to be Chamberlin–Courant. -/

open Finset BigOperators

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

theorem voterScore_le_utility (w : Weight) (n : ℕ) : voterScore w n ≤ (n : ℝ) := by
  calc
    voterScore w n ≤ ∑ _j ∈ range n, (1 : ℝ) := by
      apply sum_le_sum
      intro j _
      exact (w.decreasing (show 1 ≤ j + 1 by omega)).trans_eq w.first_eq
    _ = _ := by simp

theorem voterScore_eq_utility_of_le_one (w : Weight) {n : ℕ} (hn : n ≤ 1) :
    voterScore w n = (n : ℝ) := by interval_cases n <;> simp [voterScore, w.first_eq]

namespace FirstWeightTest

private def votes (t : ℕ) : Option (Fin t) → ℕ
  | none => t
  | some _ => 1

private theorem votes_positive {t : ℕ} (ht : 0 < t) : ∀ p, 0 < votes t p := by
  intro p
  cases p <;> simp [votes, ht]

private theorem votes_sum (t : ℕ) : ∑ p, votes t p = t + t := by simp [votes, Fintype.sum_option]

private def election (t : ℕ) : Election (Σ p, Fin (votes t p)) (Option (Fin t) × Fin 2) 2 :=
  PartyList.instanceOf (votes t) 2 (by decide)

private theorem large_seats_bound {t : ℕ} (ht : 0 < t)
    {W : Finset (Option (Fin t) × Fin 2)} (hW : SatisfiesAUQ (election t) W) :
    PartyList.seats W none ≤ 1 := by
  have h := PartyList.auq_bound (votes t) (votes_positive ht) 2 (by decide) hW none
  rw [votes_sum] at h
  have hq : (2 : ℚ) * t / (t + t) = 1 := by
    have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ht
    field_simp
    ring
  norm_num only [votes, Nat.cast_add, Nat.cast_ofNat] at h
  rw [hq] at h
  exact h

private theorem winner_score_bound {t : ℕ} (ht : 0 < t) (w : Weight)
    {W : Finset (Option (Fin t) × Fin 2)} (hcard : W.card = 2)
    (hAUQ : SatisfiesAUQ (election t) W) : thieleScore w (election t) W ≤ t + 1 := by
  have hlarge := large_seats_bound ht hAUQ
  have htotal := PartyList.sum_seats W
  simp only [Fintype.sum_option, hcard] at htotal
  have hbound : (∑ p : Fin t, voterScore w (PartyList.seats W (some p))) ≤
      ∑ p : Fin t, (PartyList.seats W (some p) : ℝ) :=
    sum_le_sum (fun i _ => voterScore_le_utility w _)
  have htotal' : (∑ p : Fin t, (PartyList.seats W (some p) : ℝ)) +
      PartyList.seats W none = 2 := by
    have h : (PartyList.seats W none : ℝ) +
        (∑ p : Fin t, (PartyList.seats W (some p) : ℝ)) = 2 := by exact_mod_cast htotal
    linarith
  have hlarge' : (PartyList.seats W none : ℝ) ≤ 1 := by exact_mod_cast hlarge
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hprod := mul_nonneg (sub_nonneg.mpr ht') (sub_nonneg.mpr hlarge')
  unfold election
  rw [PartyList.score_eq]
  simp only [Fintype.sum_option, votes, Nat.cast_one, one_mul]
  rw [voterScore_eq_utility_of_le_one w hlarge]
  nlinarith

private theorem large_committee_score (t : ℕ) (w : Weight) :
    thieleScore w (election t) (PartyList.ballot 2 none) = (t : ℝ) * (1 + w.value 2) := by
  unfold election
  rw [PartyList.score_eq]
  have hs (p : Fin t) : PartyList.seats (PartyList.ballot 2 (none : Option (Fin t))) (some p) = 0 := by
    rw [PartyList.seats, Finset.disjoint_iff_inter_eq_empty.mp (PartyList.ballot_disjoint (by simp))]
    rfl
  have hn : PartyList.seats (PartyList.ballot 2 (none : Option (Fin t))) none = 2 := by
    simp [PartyList.seats]
  simp [Fintype.sum_option, votes, hs, hn, voterScore, sum_range_succ, w.first_eq]

/-- The family of two-seat tests bounds the second marginal by `1/t`. -/
theorem second_weight_bound (ws : CompositeWeights)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) (t : ℕ) (ht : 0 < t) :
    (t : ℝ) * ws.firstWeight.value 2 ≤ 1 := by
  obtain ⟨W, hW⟩ := (compositeRule_wellFormed ws (election t)).1
  have hcard := ((compositeRule_wellFormed ws (election t)).2 W hW).1
  have htest := PartyList.is_apportionment (votes t) (votes_positive ht) 2 (by decide)
  have hbound := winner_score_bound ht ws.firstWeight hcard (hAUQ _ _ 2 _ htest W hW)
  have hfirst := (mem_selectMax.mp (composite_refines_first ws (election t) hW)).2
  have hfeas : PartyList.ballot 2 (none : Option (Fin t)) ∈ feasible (election t) := by
    rw [mem_feasible, PartyList.card_ballot]
  have hmax := hfirst _ hfeas
  rw [large_committee_score] at hmax
  nlinarith

end FirstWeightTest

/-- Step 1 of thesis Theorem 3.6, with one weight sequence fixed across all sizes. -/
theorem first_weight_eq_CC_of_AUQ (ws : CompositeWeights)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) : ws.firstWeight = ccWeight := by
  apply weight_eq_cc_of_second_zero
  apply le_antisymm _ (ws.firstWeight.nonneg 2)
  by_contra! hpos
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / ws.firstWeight.value 2) 1)
  have htpos : 0 < t := by
    have h : (1 : ℝ) < t := (le_max_right _ _).trans_lt ht
    exact_mod_cast (show (0 : ℝ) < t by linarith)
  have hlarge : 1 < (t : ℝ) * ws.firstWeight.value 2 :=
    (div_lt_iff₀ hpos).mp ((le_max_left _ _).trans_lt ht)
  linarith [FirstWeightTest.second_weight_bound ws hAUQ t htpos]

end

section

/-! Finding the first non-CC stage under AUQ, including infinite sequences. -/

open Finset

/-- For internal indexing only: finite sequences are padded by CC after ending.
The rule still uses its original finite-stage definition. -/
def CompositeWeights.weightAt : CompositeWeights → ℕ → Weight
  | .finite first rest, n => (first :: rest)[n]?.getD ccWeight
  | .infinite weights, n => weights n

@[simp] theorem weightAt_zero (ws : CompositeWeights) : ws.weightAt 0 = ws.firstWeight := by cases ws <;> rfl

variable {V C : Type*} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

theorem selectMax_idempotent {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    selectMax (selectMax s f) f = selectMax s f := by
  apply Subset.antisymm (selectMax_subset _ _)
  intro x hx
  apply mem_selectMax.mpr
  exact ⟨hx, fun y hy => (mem_selectMax.mp hx).2 y ((mem_selectMax.mp hy).1)⟩

theorem applyStage_eq_of_active (ws : CompositeWeights) (E : Election V C k)
    (n : ℕ) (s : Finset (Finset C)) (hactive : ws.weightAt n ≠ ccWeight) :
    applyStage ws E n s = selectMax s (thieleScore (ws.weightAt n) E) := by
  cases ws with
  | infinite weights => rfl
  | finite first rest =>
    by_cases h : n < (first :: rest).length
    · have hget : (first :: rest)[n]?.getD ccWeight = (first :: rest)[n] := by
        rw [List.getElem?_eq_getElem h]
        rfl
      simp only [applyStage, dif_pos h, CompositeWeights.weightAt, hget]
    · have hn : (first :: rest)[n]? = none := List.getElem?_eq_none (by omega)
      simp [CompositeWeights.weightAt, hn] at hactive

/-- A CC stage acting on CC winners does not change the winner set. -/
theorem applyStage_CC_on_CC (ws : CompositeWeights) (E : Election V C k) (n : ℕ)
    (hcc : ws.weightAt n = ccWeight) :
    applyStage ws E n (thieleRule ccWeight E) = thieleRule ccWeight E := by
  cases ws with
  | infinite weights =>
    change selectMax (selectMax (feasible E) (thieleScore ccWeight E))
      (thieleScore (weights n) E) = _
    change weights n = ccWeight at hcc
    rw [hcc, selectMax_idempotent]
    rfl
  | finite first rest =>
    by_cases h : n < (first :: rest).length
    · have hw : (first :: rest)[n] = ccWeight := by
        change (first :: rest)[n]?.getD ccWeight = ccWeight at hcc
        rw [List.getElem?_eq_getElem h] at hcc
        exact hcc
      simp only [applyStage, dif_pos h, hw]
      exact selectMax_idempotent _ _
    · simp only [applyStage, dif_neg h]

/-- All stages before a first non-CC weight have exactly the CC winner set. -/
theorem stage_eq_CC_of_prefix (ws : CompositeWeights) (E : Election V C k)
    (hfirst : ws.firstWeight = ccWeight) (n : ℕ)
    (hprefix : ∀ j < n, ws.weightAt j = ccWeight) (hn : 0 < n) :
    thieleStage ws E n = thieleRule ccWeight E := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      have hstage : thieleStage ws E 1 = thieleRule ws.firstWeight E := by
        cases ws <;> rfl
      rw [hstage, hfirst]
    · rw [thieleStage, ih (fun j hj => hprefix j (by omega)) (by omega)]
      exact applyStage_CC_on_CC ws E n (hprefix n (by omega))

/-- The retained first effective score must be maximized among CC winners. -/
def EffectiveWeight (ws : CompositeWeights) (w : Weight) : Prop :=
  ∀ (V C : Type) [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] (k : ℕ)
    (E : Election V C k) W, W ∈ compositeRule ws E →
      W ∈ selectMax (thieleRule ccWeight E) (thieleScore w E)

/-- AUQ forces a finite first non-CC stage, even for an infinite composite. -/
theorem exists_effective_weight (ws : CompositeWeights)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) :
    ∃ w, 0 < w.value 2 ∧ EffectiveWeight ws w := by
  classical
  have hfirst := first_weight_eq_CC_of_AUQ ws hAUQ
  have hex : ∃ n, ws.weightAt n ≠ ccWeight := by
    by_contra! hall
    have hbad : ({0, 1, 3} : Finset (Fin 6)) ∈
        compositeRule ws CharacterizationExamples.twoPartyInstance := by
      apply (mem_compositeRule _ _ _).mpr
      intro n
      cases n with
      | zero => rw [thieleStage, mem_feasible]; decide
      | succ n =>
        rw [stage_eq_CC_of_prefix ws _ hfirst (n + 1) (fun j _ => hall j) (by omega)]
        exact CharacterizationExamples.bad_committee_wins_CC
    exact CharacterizationExamples.bad_committee_fails_AUQ
      (hAUQ _ _ 3 _ CharacterizationExamples.twoParty_is_apportionment _ hbad)
  let n := Nat.find hex
  have hnweight : ws.weightAt n ≠ ccWeight := Nat.find_spec hex
  have hprefix : ∀ j < n, ws.weightAt j = ccWeight := by
    intro j hj
    exact not_not.mp (Nat.find_min hex hj)
  have hn : 0 < n := by
    by_contra! hz
    have hz' : n = 0 := by omega
    simp [hz', hfirst] at hnweight
  refine ⟨ws.weightAt n, ?_, ?_⟩
  · have hnonneg := (ws.weightAt n).nonneg 2
    by_contra! h
    exact hnweight (weight_eq_cc_of_second_zero _ (le_antisymm h hnonneg))
  · intro V C _ _ _ _ k E W hW
    have h := (mem_compositeRule ws E W).mp hW (n + 1)
    rw [thieleStage, stage_eq_CC_of_prefix ws E hfirst n hprefix hn,
      applyStage_eq_of_active ws E n _ hnweight] at h
    exact h

end

section

/-! Marginal inequalities from one-seat transfers between parties. -/

open Finset BigOperators

namespace PartyList

variable {P : Type} [Fintype P] [DecidableEq P] [Nonempty P]

private theorem score_CC_eq_electorate (v : P → ℕ) (k : ℕ) (hk : 0 < k)
    {W : Finset (P × Fin k)} (hcover : ∀ p, 0 < seats W p) :
    thieleScore ccWeight (instanceOf v k hk) W = Fintype.card (Σ p, Fin (v p)) := by
  rw [score_eq, electorate_card]
  push_cast
  apply sum_congr rfl
  intro p _
  rw [voterScore_cc, if_neg (Nat.ne_of_gt (hcover p)), mul_one]

/-- With enough seats to cover all parties, every CC winner covers all parties. -/
theorem covers_all (v : P → ℕ) (hv : ∀ p, 0 < v p) (k : ℕ) (hk : 0 < k)
    (hpk : Fintype.card P ≤ k) {W : Finset (P × Fin k)}
    (hW : W ∈ thieleRule ccWeight (instanceOf v k hk)) : ∀ p, 0 < seats W p := by
  let seed : Finset (P × Fin k) := univ ×ˢ {⟨0, hk⟩}
  have hseed : seed.card ≤ k := by simpa [seed] using hpk
  obtain ⟨U, hsub, hcard⟩ := Finset.exists_superset_card_eq hseed (instanceOf v k hk).k_le_m
  have hUcover : ∀ p, 0 < seats U p := by
    intro p
    apply card_pos.mpr
    exact ⟨(p, ⟨0, hk⟩), mem_inter.mpr ⟨hsub (by simp [seed]), by simp⟩⟩
  have hUscore := score_CC_eq_electorate v k hk hUcover
  have hmax := (mem_selectMax.mp hW).2 U ((mem_feasible _ _).mpr hcard)
  rw [hUscore] at hmax
  intro p
  by_contra! hp
  have hzero : seats W p = 0 := by omega
  have hstrict : thieleScore ccWeight (instanceOf v k hk) W < Fintype.card (Σ p, Fin (v p)) := by
    rw [score_eq, electorate_card]
    push_cast
    apply sum_lt_sum
    · intro q _
      have hs : voterScore ccWeight (seats W q) ≤ 1 := by rw [voterScore_cc]; split_ifs <;> norm_num
      simpa using mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ v q)
    · refine ⟨p, mem_univ _, ?_⟩
      rw [hzero, voterScore_cc_zero, mul_zero]
      exact_mod_cast hv p
  linarith

/-- A feasible seat transfer among covered parties must not improve the effective score. -/
theorem transfer_bound (ws : CompositeWeights) (w : Weight) (heff : EffectiveWeight ws w)
    (v : P → ℕ) (hv : ∀ p, 0 < v p) (k : ℕ) (hk : 0 < k)
    {W : Finset (P × Fin k)} (hW : W ∈ compositeRule ws (instanceOf v k hk))
    (hcover : ∀ p, 0 < seats W p) {p q : P} (hpq : p ≠ q)
    (hp : 2 ≤ seats W p) (hq : seats W q < k) :
    (v q : ℝ) * w.value (seats W q + 1) ≤ (v p : ℝ) * w.value (seats W p) := by
  obtain ⟨c, hcW, hcp⟩ : ∃ c ∈ W, c.1 = p := by
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < seats W p by omega)
    exact ⟨c, (mem_inter.mp hc).1, mem_ballot.mp (mem_inter.mp hc).2⟩
  obtain ⟨d, hdq, hdW⟩ : ∃ d : P × Fin k, d.1 = q ∧ d ∉ W := by
    have hn : ¬ ballot k q ⊆ W := by
      intro hsub
      have heq : W ∩ ballot k q = ballot k q := inter_eq_right.mpr hsub
      simp only [seats, heq, card_ballot] at hq
      omega
    obtain ⟨d, hd, hdW⟩ := Finset.not_subset.mp hn
    exact ⟨d, mem_ballot.mp hd, hdW⟩
  let U := swap W c d
  have hbalance (r : P) : seats U r + (if p = r then 1 else 0) =
      seats W r + (if q = r then 1 else 0) := by
    have h := utility_swap_balance (instanceOf v k hk) hcW hdW (⟨r, ⟨0, hv r⟩⟩)
    change seats U r + (if c ∈ ballot k r then 1 else 0) =
      seats W r + (if d ∈ ballot k r then 1 else 0) at h
    simpa only [mem_ballot, hcp, hdq] using h
  have hUcover : ∀ r, 0 < seats U r := by
    intro r
    have h := hbalance r
    have hold := hcover r
    by_cases hpr : p = r
    · subst r
      simp only [ite_true, hpq.symm, ite_false, add_zero] at h
      omega
    · split_ifs at h <;> omega
  have hUcard : U.card = k :=
    (card_swap hcW hdW).trans (((compositeRule_wellFormed ws _).2 W hW).1)
  have hU : U ∈ thieleRule ccWeight (instanceOf v k hk) := by
    apply mem_selectMax.mpr
    refine ⟨(mem_feasible _ _).mpr hUcard, ?_⟩
    intro T _
    rw [score_CC_eq_electorate v k hk hUcover]
    exact cc_score_le_voters _ _
  have hmax := (mem_selectMax.mp (heff _ _ k _ W hW)).2 U hU
  have hdelta : thieleScore w (instanceOf v k hk) U - thieleScore w (instanceOf v k hk) W =
      (v q : ℝ) * w.value (seats W q + 1) - (v p : ℝ) * w.value (seats W p) := by
    rw [score_eq, score_eq, ← sum_sub_distrib]
    have hpoint (r : P) :
        (v r : ℝ) * voterScore w (seats U r) - (v r : ℝ) * voterScore w (seats W r) =
          (if r = q then (v q : ℝ) * w.value (seats W q + 1) else 0) -
          (if r = p then (v p : ℝ) * w.value (seats W p) else 0) := by
      have h := hbalance r
      by_cases hrp : r = p
      · subst r
        have hu : seats W p = seats U p + 1 := by simp [hpq.symm] at h; omega
        simp only [hpq, ite_false, ite_true, zero_sub]
        rw [hu, voterScore_succ]
        ring
      · by_cases hrq : r = q
        · subst r
          have hu : seats U q = seats W q + 1 := by simp [hpq] at h; omega
          simp only [hrp, ite_false, ite_true, sub_zero]
          rw [hu, voterScore_succ]
          ring
        · have hu : seats U r = seats W r := by
            simp only [Ne.symm hrp, Ne.symm hrq, ite_false, add_zero] at h
            exact h
          simp [hu, hrp, hrq]
    simp_rw [hpoint]
    simp [sum_sub_distrib]
  linarith

end PartyList

end

section

/-! Integer party-list replication forces the effective weight's Adams tail. -/

open Finset BigOperators

namespace TailWeightTests

private def lowerVotes (h s : ℕ) : Option (Fin h) → ℕ
  | none => h
  | some _ => h * s + 1

private theorem lower_positive {h s : ℕ} (hh : 0 < h) : ∀ p, 0 < lowerVotes h s p := by
  intro p
  cases p <;> simp [lowerVotes, hh]

private theorem lower_sum (h s : ℕ) : ∑ p, lowerVotes h s p = h * (h * s + 2) := by
  simp [lowerVotes, Fintype.sum_option]
  ring

/-- An AUQ winner must prefer an additional seat for a large party over giving
its second seat to the small party. -/
theorem lower_bound (ws : CompositeWeights) (w : Weight) (heff : EffectiveWeight ws w)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws))
    (h s : ℕ) (hh : 0 < h) (hs : 0 < s) :
    (h : ℝ) * w.value 2 ≤ (h * s + 1 : ℕ) * w.value (s + 1) := by
  let k := h * s + 2
  have hk : 0 < k := by dsimp [k]; omega
  let E := PartyList.instanceOf (lowerVotes h s) k hk
  have htest := PartyList.is_apportionment (lowerVotes h s) (lower_positive hh) k hk
  obtain ⟨W, hW⟩ := (compositeRule_wellFormed ws E).1
  have hcard := ((compositeRule_wellFormed ws E).2 W hW).1
  have hprimary := (mem_selectMax.mp (heff _ _ k E W hW)).1
  have hpk : Fintype.card (Option (Fin h)) ≤ k := by simp; dsimp [k]; nlinarith
  have hcover := PartyList.covers_all (lowerVotes h s) (lower_positive hh) k hk hpk hprimary
  have hnone := PartyList.auq_bound (lowerVotes h s) (lower_positive hh) k hk
    (hAUQ _ _ k E htest W hW) none
  have hquota : (k : ℚ) * lowerVotes h s none / (∑ p, lowerVotes h s p) = 1 := by
    rw [lower_sum]
    change (k : ℚ) * h / (h * (h * s + 2) : ℕ) = 1
    have hh' : (h : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    change (k : ℚ) * h / (h * k : ℕ) = 1
    push_cast
    field_simp
  rw [hquota] at hnone
  have hnone' : PartyList.seats W none = 1 := by
    have := hcover none
    simpa using (show PartyList.seats W none = 1 by norm_num at hnone; omega)
  have htotal := PartyList.sum_seats W
  simp only [Fintype.sum_option, hnone', hcard] at htotal
  obtain ⟨i, hi⟩ : ∃ i : Fin h, s + 1 ≤ PartyList.seats W (some i) := by
    by_contra! hall
    have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin h)))
      (fun i _ => show PartyList.seats W (some i) ≤ s by have hi := hall i; omega)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    dsimp [k] at htotal
    omega
  have htransfer := PartyList.transfer_bound ws w heff (lowerVotes h s)
    (lower_positive hh) k hk hW hcover (p := some i) (q := none) (by simp)
    (by omega) (by rw [hnone']; dsimp [k]; omega)
  rw [hnone'] at htransfer
  simp only [lowerVotes] at htransfer
  have hmono := w.decreasing hi
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ h * s + 1)
  push_cast at htransfer ⊢
  linarith

private def upperVotes (h s : ℕ) : Option (Fin (h * s)) → ℕ
  | none => h * s - 1
  | some _ => h

private theorem upper_positive {h s : ℕ} (hh : 2 ≤ h) (hs : 0 < s) :
    ∀ p, 0 < upperVotes h s p := by
  intro p
  cases p <;> simp only [upperVotes]
  · have : 2 ≤ h * s := by nlinarith
    omega
  · omega

private theorem upper_sum (h s : ℕ) :
    ∑ p, upperVotes h s p = h * s - 1 + h * s * h := by simp [upperVotes, Fintype.sum_option]

/-- Moving a seat into the large party bounds its next marginal from above. -/
theorem upper_bound (ws : CompositeWeights) (w : Weight) (heff : EffectiveWeight ws w)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) (hw : 0 < w.value 2)
    (hlower : ∀ s : ℕ, 0 < s → w.value 2 ≤ (s : ℝ) * w.value (s + 1))
    (h s : ℕ) (hh : 2 ≤ h) (hs : 0 < s) :
    (h * s - 1 : ℕ) * w.value (s + 1) ≤ (h : ℝ) * w.value 2 := by
  let g := h * s
  let k := g + s + 1
  have hg : 2 ≤ g := by dsimp [g]; nlinarith
  have hk : 0 < k := by dsimp [k]; omega
  let E := PartyList.instanceOf (upperVotes h s) k hk
  have htest := PartyList.is_apportionment (upperVotes h s) (upper_positive hh hs) k hk
  obtain ⟨W, hW⟩ := (compositeRule_wellFormed ws E).1
  have hcard := ((compositeRule_wellFormed ws E).2 W hW).1
  have hprimary := (mem_selectMax.mp (heff _ _ k E W hW)).1
  have hpk : Fintype.card (Option (Fin (h * s))) ≤ k := by simp; dsimp [k, g]; omega
  have hcover := PartyList.covers_all (upperVotes h s) (upper_positive hh hs) k hk hpk hprimary
  have hnone := PartyList.auq_bound (upperVotes h s) (upper_positive hh hs) k hk
    (hAUQ _ _ k E htest W hW) none
  have hquota : (k : ℚ) * upperVotes h s none / (∑ p, upperVotes h s p) ≤ (s : ℚ) := by
    rw [upper_sum]
    have hgq : (1 : ℚ) ≤ h * s := by exact_mod_cast (show 1 ≤ h * s by omega)
    have hsub : ((h * s - 1 : ℕ) : ℚ) = (h : ℚ) * s - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ h * s)]
      push_cast
      ring
    have hden : (0 : ℚ) < (h * s - 1 + h * s * h : ℕ) := by
      exact_mod_cast (show 0 < h * s - 1 + h * s * h by omega)
    apply (div_le_iff₀ hden).mpr
    dsimp [k, g, upperVotes]
    push_cast
    rw [hsub]
    nlinarith
  have hseat : PartyList.seats W none ≤ s := hnone.trans (Nat.ceil_le.mpr hquota)
  have hnone_eq : PartyList.seats W none = s := by
    by_contra hne
    have hlt : PartyList.seats W none < s := by omega
    have htotal := PartyList.sum_seats W
    simp only [Fintype.sum_option, hcard] at htotal
    obtain ⟨i, hi⟩ : ∃ i : Fin (h * s), 2 ≤ PartyList.seats W (some i) := by
      by_contra! hall
      have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin (h * s))))
        (fun i _ => show PartyList.seats W (some i) ≤ 1 by have hi := hall i; omega)
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
      dsimp [k, g] at htotal
      omega
    have htransfer := PartyList.transfer_bound ws w heff (upperVotes h s)
      (upper_positive hh hs) k hk hW hcover (p := some i) (q := none) (by simp) hi
      (by dsimp [k]; omega)
    have hl := hlower (PartyList.seats W none) (hcover none)
    have hincpos : 0 < w.value (PartyList.seats W none + 1) := by
      have := w.nonneg (PartyList.seats W none + 1)
      nlinarith [show (0 : ℝ) ≤ PartyList.seats W none by positivity]
    have hmono := w.decreasing hi
    simp only [upperVotes] at htransfer
    have hbound := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ h)
    have hsub : h * s - 1 + 1 = h * s := Nat.sub_add_cancel (by omega)
    have hgap : (h : ℝ) * PartyList.seats W none < (h * s - 1 : ℕ) := by
      have hnat : h * PartyList.seats W none < h * s - 1 := by nlinarith
      exact_mod_cast hnat
    have hstrict := mul_lt_mul_of_pos_right hgap hincpos
    have hlowmul := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ h)
    nlinarith
  have htotal := PartyList.sum_seats W
  simp only [Fintype.sum_option, hnone_eq, hcard] at htotal
  obtain ⟨i, hi⟩ : ∃ i : Fin (h * s), 2 ≤ PartyList.seats W (some i) := by
    by_contra! hall
    have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin (h * s))))
      (fun i _ => show PartyList.seats W (some i) ≤ 1 by have hi := hall i; omega)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
    dsimp [k, g] at htotal
    omega
  have htransfer := PartyList.transfer_bound ws w heff (upperVotes h s)
    (upper_positive hh hs) k hk hW hcover (p := some i) (q := none) (by simp) hi
    (by rw [hnone_eq]; dsimp [k]; omega)
  rw [hnone_eq] at htransfer
  simp only [upperVotes] at htransfer
  have hmono := w.decreasing hi
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ h)
  linarith

/-- An Archimedean argument replaces limits as the replication factor grows. -/
private theorem le_of_replication {x y z : ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → (n : ℝ) * x ≤ (n : ℝ) * y + z) : x ≤ y := by
  by_contra! hgt
  have hd : 0 < x - y := sub_pos.mpr hgt
  obtain ⟨n, hn⟩ := exists_nat_gt (max (z / (x - y)) 2)
  have hn2 : 2 ≤ n := by
    have ht := (le_max_right _ _).trans_lt hn
    exact_mod_cast (le_of_lt ht)
  have hprod : z < (n : ℝ) * (x - y) :=
    (div_lt_iff₀ hd).mp ((le_max_left _ _).trans_lt hn)
  linarith [h n hn2]

/-- The lower tests force the Adams marginal ratios from below. -/
theorem tail_lower (ws : CompositeWeights) (w : Weight) (heff : EffectiveWeight ws w)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) (s : ℕ) (hs : 0 < s) :
    w.value 2 ≤ (s : ℝ) * w.value (s + 1) := by
  apply le_of_replication (z := w.value (s + 1))
  intro h hh
  have htest := lower_bound ws w heff hAUQ h s (by omega) hs
  push_cast at htest
  nlinarith

/-- The two integer test families force all effective tail weights, up to scale. -/
theorem tail_eq (ws : CompositeWeights) (w : Weight) (heff : EffectiveWeight ws w)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) (hw : 0 < w.value 2)
    (s : ℕ) (hs : 0 < s) : (s : ℝ) * w.value (s + 1) = w.value 2 := by
  apply le_antisymm _ (tail_lower ws w heff hAUQ s hs)
  apply le_of_replication (z := w.value (s + 1))
  intro h hh
  have htest := upper_bound ws w heff hAUQ hw (tail_lower ws w heff hAUQ) h s hh hs
  rw [Nat.cast_sub (by nlinarith : 1 ≤ h * s)] at htest
  push_cast at htest
  nlinarith

end TailWeightTests

end

section

/-! Theorem 3.6 and the resulting global JUQ characterization. -/

open Finset BigOperators

/-- The first non-CC stage differs from Adams' secondary score only by a positive
scale and a multiple of the CC score. The latter is constant among CC winners. -/
theorem voterScore_affine_adams (w : Weight)
    (htail : ∀ s : ℕ, 0 < s → (s : ℝ) * w.value (s + 1) = w.value 2) (t : ℕ) :
    voterScore w t = w.value 2 * voterScore adamsWeight t +
      (1 - w.value 2) * voterScore ccWeight t := by
  induction t with
  | zero => simp [voterScore]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [voterScore, w.first_eq, adamsWeight, ccWeight]
    · have hnpos : 0 < n := by omega
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hval : w.value (n + 1) = w.value 2 * adamsWeight.value (n + 1) := by
        rw [adamsWeight_value _ (by omega)]
        have hcast : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
        rw [hcast, mul_one_div]
        apply (eq_div_iff hnreal).mpr
        nlinarith [htail n hnpos]
      have hcc : ccWeight.value (n + 1) = 0 := by simp [ccWeight]; omega
      rw [voterScore_succ, voterScore_succ, voterScore_succ, ih, hval, hcc]
      ring

variable {V C : Type} [Fintype V] [Fintype C]
  [DecidableEq V] [DecidableEq C] {k : ℕ}

theorem thieleScore_affine_adams (w : Weight)
    (htail : ∀ s : ℕ, 0 < s → (s : ℝ) * w.value (s + 1) = w.value 2)
    (E : Election V C k) (W : Finset C) :
    thieleScore w E W = w.value 2 * thieleScore adamsWeight E W +
      (1 - w.value 2) * thieleScore ccWeight E W := by
  simp only [thieleScore, voterScore_affine_adams w htail, sum_add_distrib, mul_sum]

/-- Once AUQ forces the effective tail weights, all final winners are Adams-Thiele winners. -/
theorem effective_weight_refines_adams (ws : CompositeWeights) (w : Weight)
    (heff : EffectiveWeight ws w) (hw : 0 < w.value 2)
    (htail : ∀ s : ℕ, 0 < s → (s : ℝ) * w.value (s + 1) = w.value 2) :
    RawRefines (compositeRule ws : Election.RawRule V C k) adamsThiele := by
  intro E W hW
  have h := heff _ _ k E W hW
  obtain ⟨hCC, hmax⟩ := mem_selectMax.mp h
  apply (mem_adamsThiele E W).mpr
  apply mem_selectMax.mpr
  refine ⟨hCC, ?_⟩
  intro U hU
  have hfeasW := (mem_selectMax.mp hCC).1
  have hfeasU := (mem_selectMax.mp hU).1
  have hccWU := (mem_selectMax.mp hU).2 W hfeasW
  have hccUW := (mem_selectMax.mp hCC).2 U hfeasU
  have hccEq : thieleScore ccWeight E U = thieleScore ccWeight E W := le_antisymm hccUW hccWU
  have hscore := hmax U hU
  rw [thieleScore_affine_adams w htail, thieleScore_affine_adams w htail, hccEq] at hscore
  nlinarith

/-- Necessity in thesis Theorem 3.6 (paper Theorem 6). No main-result hypotheses remain. -/
theorem AUQ_implies_refines_adams (ws : CompositeWeights)
    (hAUQ : FamilySatisfiesAUQ (compositeFamily ws)) :
    FamilyRefines (compositeFamily ws) adamsFamily := by
  obtain ⟨w, hw, heff⟩ := exists_effective_weight ws hAUQ
  have htail := TailWeightTests.tail_eq ws w heff hAUQ hw
  intro V C _ _ _ _ k E _ W hW
  exact effective_weight_refines_adams ws w heff hw htail E hW

/-- Thesis Theorem 3.6 / paper Theorem 6, on the agreed general domain. -/
theorem upperQuotaCharacterization (ws : CompositeWeights) : UpperQuotaCharacterization ws :=
  ⟨AUQ_implies_refines_adams ws, refinement_adamsFamily_satisfies_auq⟩

/-- The desired JUQ characterization: uniqueness up to refinement in the composite class. -/
theorem juqCharacterization (ws : CompositeWeights) : JUQCharacterization ws :=
  juqCharacterization_of_upperQuota ws (upperQuotaCharacterization ws) adamsFamily_satisfies_juq

end

end JUQLean.Internal

section

/-!
# Bridge to the author-written interface

Scores, quotas, swaps, and finite or infinite compositions are connected explicitly
to the internal development. The interface imports this file, so the correspondence
is checked through its proof applications rather than assumed.
-/

namespace JUQLean.Proofs

open JUQLean.Internal

open Finset BigOperators

/- The following formulas mirror the author's interface definitionally. The final
   one-line application in Interface checks this correspondence in Lean. -/
private def score (m n : ℕ) (profile : Fin n → Finset (Fin m))
    (w : ℕ+ → NNReal) (W : Finset (Fin m)) : NNReal :=
  ∑ i : Fin n, ∑ j ∈ range ((profile i ∩ W).card), w j.succPNat

private def supporters (m n : ℕ) (profile : Fin n → Finset (Fin m)) (c : Fin m) :=
  {i ∈ (univ : Finset (Fin n)) | c ∈ profile i}

private def committeeJUQ (m n k : ℕ) (profile : Fin n → Finset (Fin m)) (W : Finset (Fin m)) : Prop :=
  ∀ c ∈ W,
    (∀ i ∈ supporters m n profile c,
      (profile i ∩ W).card > Nat.ceil (((supporters m n profile c).card : ℚ) / n * k)) →
    ¬ ∃ (d : Fin m) (S : Finset (Fin n)),
      d ∉ W ∧ S.card > 0 ∧ S ⊆ supporters m n profile d ∧
      ∀ i ∈ S, (profile i ∩ ((W ∪ {d}) \ {c})).card ≤ Nat.ceil ((S.card : ℚ) / n * k)

private theorem weights_antitone (w : ℕ+ → NNReal)
    (hw : ∀ i : ℕ+, w i ≥ w (i + 1)) : Antitone (fun j : ℕ => w j.succPNat) := by
  apply antitone_nat_of_succ_le
  intro j
  exact hw j.succPNat

/-- Extend positive-index NNReal weights by an unused zeroth coordinate. -/
private def toWeight (w : ℕ+ → NNReal)
    (hw : w 1 = 1 ∧ ∀ i : ℕ+, w i ≥ w (i + 1)) : Weight where
  value n := if n = 0 then 1 else (w (n - 1).succPNat : ℝ)
  zero_eq := by simp
  first_eq := by
    change (w 1 : ℝ) = 1
    exact_mod_cast hw.1
  nonneg n := by split_ifs <;> positivity
  decreasing := by
    intro a b hab
    have hm := weights_antitone w hw.2
    by_cases ha : a = 0
    · subst a
      simp only [ite_true]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ite_false]
        have h := hm (Nat.zero_le (b - 1))
        have hw0 : w (Nat.succPNat 0) = 1 := hw.1
        change w (b - 1).succPNat ≤ w (Nat.succPNat 0) at h
        rw [hw0] at h
        exact_mod_cast h
    · have hb : b ≠ 0 := by omega
      simp only [ha, hb, ite_false]
      exact_mod_cast hm (Nat.sub_le_sub_right hab 1)

@[simp] private theorem toWeight_succ (w : ℕ+ → NNReal)
    (hw : w 1 = 1 ∧ ∀ i : ℕ+, w i ≥ w (i + 1)) (j : ℕ) :
    (toWeight w hw).value (j + 1) = (w j.succPNat : ℝ) := by simp [toWeight]

section Relabel

variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
  {m n k : ℕ}

private def relabelProfile (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m) :
    Fin n → Finset (Fin m) := fun i => (E.approves (ev.symm i)).image ec

private theorem relabel_utility (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (W : Finset C) (i : V) :
    (relabelProfile E ev ec (ev i) ∩ W.image ec).card = E.utility W i := by
  simp only [relabelProfile, ev.symm_apply_apply, ← image_inter _ _ ec.injective,
    card_image_of_injective _ ec.injective, Election.utility, inter_comm]

private theorem relabel_score (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (w : ℕ+ → NNReal) (hw : w 1 = 1 ∧ ∀ i : ℕ+, w i ≥ w (i + 1)) (W : Finset C) :
    (score m n (relabelProfile E ev ec) w (W.image ec) : ℝ) =
      thieleScore (toWeight w hw) E W := by
  unfold score thieleScore voterScore
  push_cast
  rw [← ev.sum_comp]
  simp only [relabel_utility, toWeight_succ]

private theorem relabel_supporters (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (c : C) : supporters m n (relabelProfile E ev ec) (ec c) = (E.supporters c).image ev := by
  ext i
  simp only [supporters, mem_filter, mem_univ, true_and, relabelProfile]
  rw [show i = ev (ev.symm i) from (ev.apply_symm_apply i).symm]
  simp [mem_supporters]
  constructor
  · intro hc
    exact ⟨ev.symm i, hc, ev.apply_symm_apply i⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

private theorem relabel_quota (E : Election V C k) (ev : V ≃ Fin n) (S : Finset V) :
    ((S.image ev).card : ℚ) / n * k = quota E S := by
  rw [card_image_of_injective _ ev.injective]
  have hn : Fintype.card V = n := by simpa using Fintype.card_congr ev
  unfold quota
  rw [hn]
  ring

omit [Fintype C] in
private theorem relabel_swap (ec : C ≃ Fin m) (W : Finset C) (c d : C) :
    (swap W c d).image ec = ((W.image ec ∪ {ec d}) \ {ec c}) := by
  simp only [swap, image_sdiff _ _ ec.injective, image_union, image_singleton]

private theorem relabel_JUQ (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (W : Finset C) (h : committeeJUQ m n k (relabelProfile E ev ec) (W.image ec)) :
    SatisfiesJUQ E W := by
  intro c d S hv
  apply h (ec c) (mem_image.mpr ⟨c, hv.1, rfl⟩)
  · intro i hi
    rw [relabel_supporters] at hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    rw [relabel_utility, relabel_supporters, relabel_quota E ev (E.supporters c)]
    simpa only [upperQuota] using hv.2.2.2.2.1 j hj
  · refine ⟨ec d, S.image ev, ?_, ?_, ?_, ?_⟩
    · simpa using hv.2.1
    · simpa only [card_image_of_injective _ ev.injective] using card_pos.mpr hv.2.2.1
    · rw [relabel_supporters]
      exact (image_subset_image_iff ev.injective).mpr hv.2.2.2.1
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      rw [← relabel_swap, relabel_utility, relabel_quota E ev S]
      simpa only [upperQuota] using hv.2.2.2.2.2 j hj

end Relabel

/- Bridges for the author's two Adams-Thiele weight functions. -/
private def adamsFirst : ℕ+ → NNReal :=
  fun i => if i = 1 then 1 else 0

private def adamsSecond : ℕ+ → NNReal :=
  fun i => ((if i = 1 then 1 else 1 / (i.natPred : NNRat) : NNRat) : NNReal)

private theorem adamsFirst_value (j : ℕ) :
    (adamsFirst j.succPNat : ℝ) = ccWeight.value (j + 1) := by
  cases j with
  | zero => norm_num [adamsFirst, ccWeight, show Nat.succPNat 0 = 1 from rfl]
  | succ j =>
    have hne : (j + 1).succPNat ≠ (1 : ℕ+) := by
      intro h
      have hv := congrArg PNat.val h
      change j + 1 + 1 = 1 at hv
      omega
    simp [adamsFirst, ccWeight, hne]

private theorem adamsSecond_value (j : ℕ) :
    (adamsSecond j.succPNat : ℝ) = adamsWeight.value (j + 1) := by
  cases j with
  | zero => norm_num [adamsSecond, adamsWeight, show Nat.succPNat 0 = 1 from rfl]
  | succ j =>
    have hne : (j + 1).succPNat ≠ (1 : ℕ+) := by
      intro h
      have hv := congrArg PNat.val h
      change j + 1 + 1 = 1 at hv
      omega
    rw [adamsWeight_value _ (by omega)]
    simp only [adamsSecond, hne, ite_false]
    simp [Nat.succPNat, PNat.natPred]

private theorem source_score {m n k : ℕ} (E : Election (Fin n) (Fin m) k)
    (w : ℕ+ → NNReal) (v : Weight)
    (h : ∀ j : ℕ, (w j.succPNat : ℝ) = v.value (j + 1)) (W : Finset (Fin m)) :
    (score m n E.approves w W : ℝ) = thieleScore v E W := by
  unfold score thieleScore voterScore Election.utility
  push_cast
  simp only [h, inter_comm]

private theorem source_max {m n k : ℕ} (E : Election (Fin n) (Fin m) k)
    (w : ℕ+ → NNReal) (v : Weight)
    (h : ∀ j : ℕ, (w j.succPNat : ℝ) = v.value (j + 1))
    (committees : Finset (Finset (Fin m))) :
    {W ∈ committees | ∀ U ∈ committees, score m n E.approves w U ≤ score m n E.approves w W} =
      selectMax committees (thieleScore v E) := by
  classical
  ext W
  simp only [mem_filter, mem_selectMax, ← source_score E w v h, NNReal.coe_le_coe]

set_option maxHeartbeats 800000 in
/-- The author's two successive maximizations satisfy exactly the author's JUQ
formula. The score and quota bridges above and below justify reuse of Theorem 3.5. -/
theorem adams_juq (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkm : k ≤ m) :
    ∀ profile,
      let committees := {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k}
      let first := {W ∈ committees | ∀ U ∈ committees,
        score m n profile adamsFirst U ≤ score m n profile adamsFirst W}
      ∀ W ∈ {W ∈ first | ∀ U ∈ first,
        score m n profile adamsSecond U ≤ score m n profile adamsSecond W},
        committeeJUQ m n k profile W := by
  classical
  intro profile
  dsimp only
  let E : Election (Fin n) (Fin m) k :=
    { approves := profile, k_pos := hk, k_le_m := by simpa using hkm }
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfeasible : {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k} =
      feasible E := by
    ext W
    simp
  let first := {W ∈ {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k} |
    ∀ U ∈ {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k},
      score m n E.approves adamsFirst U ≤ score m n E.approves adamsFirst W}
  have hfirst : first = selectMax (feasible E) (thieleScore ccWeight E) := by
    dsimp only [first]
    rw [hfeasible, source_max E adamsFirst ccWeight adamsFirst_value]
  change ∀ W ∈ {W ∈ first | ∀ U ∈ first,
      score m n E.approves adamsSecond U ≤ score m n E.approves adamsSecond W},
    committeeJUQ m n k profile W
  rw [hfirst,
    source_max E adamsSecond adamsWeight adamsSecond_value]
  intro W hW
  have hJUQ := adamsThiele_satisfies_juq E ((mem_adamsThiele E W).mpr hW)
  have hquota (S : Finset (Fin n)) :
      Nat.ceil ((S.card : ℚ) / n * k) = upperQuota E S := by
    unfold upperQuota quota
    congr 1
    simp only [Fintype.card_fin]
    ring
  intro c hc hbad
  rintro ⟨d, S, hd, hS, hsupp, hgood⟩
  apply hJUQ c d S
  refine ⟨hc, hd, card_pos.mp hS, hsupp, ?_, ?_⟩
  · intro i hi
    have hb := hbad i hi
    rw [hquota] at hb
    simpa only [supporters, E, Election.supporters, Election.voters,
      Election.utility, inter_comm] using hb
  · intro i hi
    have hg := hgood i hi
    rw [hquota] at hg
    simpa only [E, Election.utility, swap, inter_comm] using hg

/- Internal encodings used only to bridge finite and infinite author sequences. -/
private abbrev Proper (w : ℕ+ → NNReal) := w 1 = 1 ∧ ∀ i : ℕ+, w i ≥ w (i + 1)
private noncomputable def convert (w : ℕ+ → NNReal) : Weight := by
  classical
  exact if h : Proper w then toWeight w h else ccWeight
private theorem convert_eq (w : ℕ+ → NNReal) (h : Proper w) : convert w = toWeight w h := by
  unfold convert
  rw [dif_pos h]
private noncomputable def rawApply (m n : ℕ) (p : Fin n → Finset (Fin m))
    (ws : List (ℕ+ → NNReal)) (s : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  match ws with
  | [] => s
  | w :: rest => rawApply m n p rest {W ∈ s | ∀ U ∈ s, score m n p w U ≤ score m n p w W}
private theorem rawApply_append (m n : ℕ) (p : Fin n → Finset (Fin m))
    (a b : List (ℕ+ → NNReal)) (s : Finset (Finset (Fin m))) :
    rawApply m n p (a ++ b) s = rawApply m n p b (rawApply m n p a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons w a ih => exact ih _

private abbrev Sequence := Sum ((ℕ+ → NNReal) × List (ℕ+ → NNReal)) (ℕ → (ℕ+ → NNReal))
private def properSequence : Sequence → Prop
  | .inl (w, rest) => Proper w ∧ ∀ v ∈ rest, Proper v
  | .inr ws => ∀ i, Proper (ws i)
private noncomputable def convertSequence : Sequence → CompositeWeights
  | .inl (w, rest) => .finite (convert w) (rest.map convert)
  | .inr ws => .infinite (fun i => convert (ws i))
/-- Evaluate the author's recursion, retaining its supplied implementation. -/
private noncomputable def sequenceApply
    (run : ∀ m n : ℕ, (Fin n → Finset (Fin m)) → List (ℕ+ → NNReal) →
      Finset (Finset (Fin m)) → Finset (Finset (Fin m)))
    (m n k : ℕ) (p : Fin n → Finset (Fin m)) (ws : Sequence) : Finset (Finset (Fin m)) := by
  classical
  let committees := {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k}
  exact match ws with
  | .inl (first, rest) => run m n p (first :: rest) committees
  | .inr weights => {W ∈ committees | ∀ t : ℕ,
      W ∈ run m n p ((List.range t).map weights) committees}

private noncomputable abbrev rawComposite (m n k : ℕ)
    (p : Fin n → Finset (Fin m)) (ws : Sequence) : Finset (Finset (Fin m)) :=
  sequenceApply rawApply m n k p ws

section CompositeRelabel
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]
  {m n k : ℕ}
private theorem relabel_max (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (w : ℕ+ → NNReal) (hw : Proper w) (s : Finset (Finset C)) :
    {W ∈ s.image (fun T => T.image ec) | ∀ U ∈ s.image (fun T => T.image ec),
      score m n (relabelProfile E ev ec) w U ≤ score m n (relabelProfile E ev ec) w W} =
    (selectMax s (thieleScore (convert w) E)).image (fun T => T.image ec) := by
  classical
  have hs (T : Finset C) := relabel_score E ev ec w hw T
  rw [← convert_eq w hw] at hs
  ext U
  constructor
  · intro h
    obtain ⟨W, hW, rfl⟩ := mem_image.mp (mem_filter.mp h).1
    apply mem_image.mpr
    refine ⟨W, mem_selectMax.mpr ⟨hW, ?_⟩, rfl⟩
    intro T hT
    have ht := (mem_filter.mp h).2 (T.image ec) (mem_image.mpr ⟨T, hT, rfl⟩)
    have hr : (score m n (relabelProfile E ev ec) w (T.image ec) : ℝ) ≤
        score m n (relabelProfile E ev ec) w (W.image ec) := by exact_mod_cast ht
    simpa only [hs] using hr
  · rintro h
    obtain ⟨W, hW, rfl⟩ := mem_image.mp h
    obtain ⟨hW, hmax⟩ := mem_selectMax.mp hW
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨W, hW, rfl⟩, ?_⟩
    intro U hU
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hU
    have ht := hmax T hT
    rw [← hs T, ← hs W] at ht
    exact_mod_cast ht

private theorem relabel_feasible (E : Election V C k) (ec : C ≃ Fin m) :
    {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k} =
      (feasible E).image (fun T => T.image ec) := by
  ext U
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_feasible]
  constructor
  · intro hU
    refine ⟨U.image ec.symm, ?_, ?_⟩
    · simpa only [card_image_of_injective _ ec.symm.injective] using hU
    · simp [image_image]
  · rintro ⟨T, hT, rfl⟩
    simpa only [card_image_of_injective _ ec.injective] using hT

private theorem relabel_finite_stage (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (w : ℕ+ → NNReal) (rest : List (ℕ+ → NNReal))
    (hw : ∀ v ∈ w :: rest, Proper v) (t : ℕ) (ht : t ≤ (w :: rest).length) :
    rawApply m n (relabelProfile E ev ec) ((w :: rest).take t)
      {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k} =
    (thieleStage (.finite (convert w) (rest.map convert)) E t).image (fun T => T.image ec) := by
  induction t with
  | zero => exact relabel_feasible E ec
  | succ t ih =>
    have hlt : t < (w :: rest).length := by omega
    rw [List.take_succ_eq_append_getElem hlt, rawApply_append, ih (by omega)]
    simp only [rawApply]
    rw [relabel_max E ev ec _ (hw _ (List.getElem_mem hlt))]
    congr 1
    simp only [thieleStage, applyStage]
    rw [dif_pos (by simpa using hlt)]
    congr 2
    change convert (w :: rest)[t] = ((w :: rest).map convert)[t]'(by simpa using hlt)
    exact (List.getElem_map convert (h := by simpa using hlt)).symm

private theorem relabel_infinite_stage (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (ws : ℕ → (ℕ+ → NNReal)) (hw : ∀ i, Proper (ws i)) (t : ℕ) :
    rawApply m n (relabelProfile E ev ec) ((List.range t).map ws)
      {W ∈ (univ : Finset (Finset (Fin m))) | W.card = k} =
    (thieleStage (.infinite (fun i => convert (ws i))) E t).image (fun T => T.image ec) := by
  induction t with
  | zero => exact relabel_feasible E ec
  | succ t ih =>
    rw [List.range_succ, List.map_append, rawApply_append, ih]
    exact relabel_max E ev ec (ws t) (hw t) _

private theorem relabel_composite (E : Election V C k) (ev : V ≃ Fin n) (ec : C ≃ Fin m)
    (ws : Sequence) (hw : properSequence ws) (W : Finset C) :
    W.image ec ∈ rawComposite m n k (relabelProfile E ev ec) ws ↔
      W ∈ compositeRule (convertSequence ws) E := by
  classical
  have hinj := Finset.image_injective ec.injective
  have himg (s : Finset (Finset C)) : W.image ec ∈ s.image (fun T => T.image ec) ↔ W ∈ s := by
    simp only [mem_image, hinj.eq_iff, exists_eq_right]
  cases ws with
  | inl pair =>
    obtain ⟨w, rest⟩ := pair
    have hp : ∀ v ∈ w :: rest, Proper v := by simpa [properSequence] using hw
    change W.image ec ∈ rawApply _ _ _ (w :: rest) _ ↔
      W ∈ compositeRule (.finite (convert w) (rest.map convert)) E
    rw [← List.take_length (l := w :: rest), relabel_finite_stage E ev ec w rest hp _ le_rfl]
    rw [himg]
    simpa [finiteWeights] using
      (mem_compositeRule_finite (convert w) (rest.map convert) E W).symm
  | inr ws =>
    unfold rawComposite sequenceApply
    dsimp only
    simp only [mem_filter, mem_univ, true_and, mem_compositeRule]
    simp_rw [relabel_infinite_stage E ev ec ws hw, himg]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by simpa only [card_image_of_injective _ ec.injective] using (mem_feasible E W).mp (h 0), h⟩
end CompositeRelabel

set_option maxHeartbeats 1200000 in
/-- The global characterization, transferred to the author's finite-type formulas. -/
theorem only_adams_sequence (ws : Sequence) (hw : properSequence ws)
    (hall : ∀ m n k : ℕ, 0 < n ∧ 0 < k ∧ k ≤ m →
      ∀ p, ∀ W ∈ rawComposite m n k p ws, committeeJUQ m n k p W) :
    ∀ m n k : ℕ, 0 < n ∧ 0 < k ∧ k ≤ m →
      ∀ p, rawComposite m n k p ws ⊆
        rawComposite m n k p (.inl (adamsFirst, [adamsSecond])) := by
  have hg : FamilySatisfiesJUQ (compositeFamily (convertSequence ws)) := by
    intro V C _ _ _ _ k E hE W hW
    let ev := Fintype.equivFin V
    let ec := Fintype.equivFin C
    apply relabel_JUQ E ev ec W
    apply hall (Fintype.card C) (Fintype.card V) k ⟨hE, E.k_pos, E.k_le_m⟩
    exact (relabel_composite E ev ec ws hw W).mpr hW
  have href := (juqCharacterization (convertSequence ws)).mp hg
  intro m n k h p W hW
  let E : Election (Fin n) (Fin m) k :=
    { approves := p, k_pos := h.2.1, k_le_m := by simpa using h.2.2 }
  have hid : relabelProfile E (Equiv.refl _) (Equiv.refl _) = p := by
    funext i
    simp [relabelProfile, E]
  have hsource : W ∈ compositeRule (convertSequence ws) E := by
    apply (relabel_composite E (Equiv.refl _) (Equiv.refl _) ws hw W).mp
    simpa [hid] using hW
  have ha := href (Fin n) (Fin m) k E (by simpa [GeneralProfile] using h.1) hsource
  change W ∈ rawApply m n E.approves [adamsFirst, adamsSecond]
    {U ∈ (univ : Finset (Finset (Fin m))) | U.card = k}
  have hf : {U ∈ (univ : Finset (Finset (Fin m))) | U.card = k} = feasible E := by
    ext U
    simp
  simp only [rawApply]
  rw [hf, source_max E adamsFirst ccWeight adamsFirst_value,
    source_max E adamsSecond adamsWeight adamsSecond_value]
  exact (mem_adamsThiele E W).mp ha

/-- The interface supplies only its two defining recursion equations. All
induction and finite/infinite sequence transport stay in the proof module. -/
theorem only_adams_of_recursion
    (run : ∀ m n : ℕ, (Fin n → Finset (Fin m)) → List (ℕ+ → NNReal) →
      Finset (Finset (Fin m)) → Finset (Finset (Fin m)))
    (hnil : ∀ m n p s, run m n p [] s = s)
    (hcons : ∀ m n p w rest s, run m n p (w :: rest) s =
      run m n p rest {W ∈ s | ∀ U ∈ s, score m n p w U ≤ score m n p w W})
    (ws : Sequence) (hw : properSequence ws)
    (hall : ∀ m n k : ℕ, 0 < n ∧ 0 < k ∧ k ≤ m →
      ∀ p, ∀ W ∈ sequenceApply run m n k p ws, committeeJUQ m n k p W) :
    ∀ m n k : ℕ, 0 < n ∧ 0 < k ∧ k ≤ m →
      ∀ p, sequenceApply run m n k p ws ⊆
        sequenceApply run m n k p (.inl (adamsFirst, [adamsSecond])) := by
  have hrun : run = rawApply := by
    funext m n p weights committees
    induction weights generalizing committees with
    | nil => exact hnil m n p committees
    | cons w rest ih => rw [hcons, rawApply, ih]
  subst run
  exact only_adams_sequence ws hw hall

/-- Run the interface connection here, so its theorem needs only one line.
The identifier is resolved when the tactic is used in the author's interface;
this module does not import or alter the author's definitions. -/
elab "prove_only_adams_juq" : tactic => do
  let run := Lean.mkIdent `JUQLean.applyWeights
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (intro ws hw hall
     cases ws with
     | finite first rest =>
       exact JUQLean.Proofs.only_adams_of_recursion $run
         (by intros; rfl) (by intros; rfl) (.inl (first, rest)) hw hall
     | infinite weights =>
       exact JUQLean.Proofs.only_adams_of_recursion $run
         (by intros; rfl) (by intros; rfl) (.inr weights) hw hall)))

end JUQLean.Proofs

end
