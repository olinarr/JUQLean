import Mathlib
import Proofs

/-!
# Justified upper quota and Adams-Thiele

Oliviero Nardi wrote the definitions and theorem statements in this interface.
The proofs were autoformalised with Codex and are checked by Lean. They use the
local Mathlib-only development in `Proofs.lean` and may differ from the published proofs.
See `definitions.pdf` for the mathematics and source references.

Parameters are ordered `m n k`: candidates, voters, and target size. Profiles may
contain empty ballots and unsupported candidates. The main results assume a
nonempty electorate and `0 < k ≤ m`; every assumption is explicit in each statement.
-/

namespace JUQLean

/-- Voters are labelled `0, …, n - 1`. -/
abbrev Voters (n : ℕ) := Fin n

/-- Candidates are labelled `0, …, m - 1`. -/
abbrev Candidates (m : ℕ) := Fin m

/-- A finite set of candidates, used for ballots and committees. -/
abbrev SetOfCands (m : ℕ) := Finset (Candidates m)

/-- An irresolute outcome: a finite collection of committees. -/
abbrev Outcome (m : ℕ) := Finset (SetOfCands m)

/-- A rule function at fixed candidate and voter counts. Nonemptiness and size bounds
are checked separately, rather than built into this function type. -/
abbrev QuasiABCRule (m n : ℕ) := (Voters n → SetOfCands m) → Outcome m

variable (m n k : ℕ)
variable (profile : Voters n → SetOfCands m)

/-- A refinement only breaks ties: each committee it returns is also returned
by the original rule, on every profile of these sizes. -/
def refines (smaller bigger : QuasiABCRule m n) : Prop :=
  ∀ profile, (smaller profile) ⊆ (bigger profile)

open scoped NNReal

/-- Marginal weights are indexed by positive integers and take nonnegative real values. -/
abbrev WeightFunction := ℕ+ → ℝ≥0

/-- Normalise the first marginal to one and require decreasing weights. -/
def isProperWeight (w : WeightFunction) :=
  (w 1) = 1 ∧
  ∀ i : ℕ+, w i ≥ w (i + 1)

/-- Sum each voter's marginal weights over her approved committee members.
The zero-based index `j` gives the positive weight index `j.succPNat`. -/
def thieleScore (w : WeightFunction) (committee : SetOfCands m) : ℝ≥0 :=
  ∑ i : Voters n,
    ∑ j ∈ Finset.range ((profile i ∩ committee).card), w j.succPNat

/-- The full set of voters approving candidate `c`. -/
def supporters (c : Candidates m) : Finset (Voters n) :=
  {i ∈ (Finset.univ : Finset (Voters n)) | c ∈ profile i}

/-- The candidate's quota: `|supporters(c)| / n * k`, computed in the rationals. -/
def quota (c : Candidates m) : ℚ :=
  (supporters m n profile c).card / n * k

/-- The ceiling of the candidate's quota, as a natural number. -/
def upperquota (c : Candidates m) : ℕ :=
  Nat.ceil (quota m n k profile c)

/-- Justified upper quota (thesis Definition 3.9). A selected candidate whose
supporters are all above upper quota cannot be replaced by an unselected candidate
for a nonempty group whose members would all be at or below their group upper quota. -/
def JUQ_committee (W : SetOfCands m) : Prop :=
  ∀ c ∈ W,
    (∀ i ∈ supporters m n profile c,
      (profile i ∩ W).card > upperquota m n k profile c) →
    ¬ ∃ (d : Candidates m) (S : Finset (Voters n)),
      d ∉ W ∧ S.card > 0 ∧ S ⊆ supporters m n profile d ∧
      ∀ i ∈ S, (profile i ∩ ((W ∪ {d}) \ {c})).card ≤
        Nat.ceil ((S.card : ℚ) / n * k)

/-- Every winning committee satisfies JUQ, on every profile of these sizes. -/
def JUQ_rule (scw : QuasiABCRule m n) : Prop :=
  ∀ profile, ∀ W ∈ scw profile, JUQ_committee m n k profile W

/-- A finite, nonempty sequence of weights, or an infinite sequence.
There are no empty composites or skipped stages. -/
inductive WeightSequence where
  | finite (first : WeightFunction) (rest : List WeightFunction)
  | infinite (weights : ℕ → WeightFunction)

/-- Every weight function in the sequence is normalised and decreasing. -/
def areProperWeights (ws : WeightSequence) : Prop :=
  match ws with
  | .finite first rest => isProperWeight first ∧ ∀ w ∈ rest, isProperWeight w
  | .infinite weights   => ∀ i : ℕ, isProperWeight (weights i)

/-- Apply weights in order, using each next score to break the remaining ties. -/
noncomputable def applyWeights
    (ws : List WeightFunction) (committees : Outcome m) : Outcome m :=
  match ws with
  | [] => committees
  | w :: rest =>
      applyWeights rest
        {W ∈ committees | ∀ other ∈ committees,
          thieleScore m n profile w other ≤ thieleScore m n profile w W}

/-- Start with all size-`k` committees and apply the sequence. For an infinite sequence,
keep exactly the committees surviving every finite prefix, including the empty prefix. -/
noncomputable def CompositeThiele (ws : WeightSequence) : Outcome m :=
  let committees := {W ∈ (Finset.univ : Outcome m) | W.card = k}
  match ws with
  | .finite first rest =>
      applyWeights m n profile (first :: rest) committees
  | .infinite weights => by
      classical
      exact {W ∈ committees | ∀ t : ℕ,
        W ∈ applyWeights m n profile ((List.range t).map weights) committees}

/-- Get the composite Thiele rule given a certain weight sequeence. -/
noncomputable def getCompositeThiele (ws : WeightSequence) : QuasiABCRule m n :=
  fun profile => CompositeThiele m n k profile ws

/-- The primary Adams-Thiele weights `(1, 0, 0, …)`: maximise the number of covered voters. -/
def w1 : WeightFunction :=
  fun i => if i = 1 then 1 else 0

/-- The secondary Adams-Thiele weights `(1, 1, 1/2, 1/3, …)`. Rational arithmetic
supplies these exact values before casting to nonnegative reals. -/
def w2 : WeightFunction :=
  fun i =>
    ((if i = 1 then 1 else 1 / (i.natPred : NNRat) : NNRat) : NNReal)

/-- Adams-Thiele: first maximise coverage, then apply the secondary weights. -/
noncomputable def AdamsThiele : QuasiABCRule m n :=
  getCompositeThiele m n k (WeightSequence.finite w1 [w2])

/-- Adams-Thiele satisfies JUQ on every nonempty electorate with an admissible positive size.
This is the Adams-Thiele case of thesis Theorem 3.5. -/
theorem AdamsJUQ :
    ∀ m n k : ℕ, n > 0 ∧ k > 0 ∧ k ≤ m →
    JUQ_rule m n k (AdamsThiele m n k) := by
  exact fun m n k h => Proofs.adams_juq m n k h.1 h.2.1 h.2.2

/-- The global JUQ characterisation among composite Thiele rules, up to refinement.
One proper sequence is fixed before quantifying over all election sizes.
Assuming JUQ only at a single size would not express this characterisation.
The supporting characterisation is thesis Theorem 3.6. -/
theorem OnlyAdamsJUQ :
    ∀ ws : WeightSequence, areProperWeights ws →
      (∀ m n k : ℕ, n > 0 ∧ k > 0 ∧ k ≤ m →
        JUQ_rule m n k (getCompositeThiele m n k ws)) →
      ∀ m n k : ℕ, n > 0 ∧ k > 0 ∧ k ≤ m →
        refines m n
          (getCompositeThiele m n k ws)
          (AdamsThiele m n k) := by
  prove_only_adams_juq

end JUQLean
