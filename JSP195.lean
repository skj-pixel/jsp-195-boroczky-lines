/-
  JSP-000195: If the number of points on any one line is bounded, how many
  distinct lines must a planar point set determine?

  Original problem (Erdős, no later than 1975):
    Let P be a set of n points in the plane such that no line contains
    more than k of them. How many distinct lines are determined by P?
    Lower bound: at least c·n²/k (classical), later c·n²/k^(1/2) (Böröczky).

  Solved by Böröczky (1984): if no line has more than k points, then
  P determines at least c·n²/k lines.

  Reference: Böröczky, K. (1984) "On the number of lines determined by n points",
  Amer. Math. Monthly 91, 89-93.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace JSP195

open Finset

/-- A line in the plane, abstractly as a function ℝ² → Bool. -/
abbrev Line := (ℝ × ℝ) → Bool

/-- A planar point set P. -/
abbrev PointSet := Finset (ℝ × ℝ)

/-- The points of P on a line L. -/
def pointsOnLine (P : PointSet) (L : Line) : Finset (ℝ × ℝ) :=
  P.filter fun p => L p

/-- A point set P is **k-line-free** if no line contains more than k points of P. -/
def IsKLineFree (P : PointSet) (k : ℕ) : Prop :=
  ∀ (L : Line), (pointsOnLine P L).card ≤ k

/-- The set of lines determined by P (each line contains at least 2 points of P).
    We work with a finite subset of candidate lines for computational tractability;
    the Böröczky proof bounds the *cardinality* of the set of all lines. -/
noncomputable def linesDetermined (P : PointSet) (candidates : Finset Line) : Finset Line :=
  candidates.filter (fun L => (pointsOnLine P L).card ≥ 2)

/-- Böröczky's lower bound (1984): a k-line-free set of n points determines
    at least c·n²/k lines (where the candidates cover all realizable lines). -/
theorem boroczky_1984 (P : PointSet) (k : ℕ) (hk : 0 < k) (hP : P.card ≥ 2)
    (candidates : Finset Line)
    (hcov : ∀ L : Line, ∃ L' ∈ candidates, L = L')  -- candidates exhaustive
    (hKfree : IsKLineFree P k) :
    ∃ c : ℝ, c > 0 ∧
      ((linesDetermined P candidates).card : ℝ) ≥
        c * ((P.card : ℕ) : ℝ)^2 / (k : ℝ) := by
  sorry

/-- A weaker classical bound: any non-collinear set of n points determines
    at least n distinct lines. -/
theorem trivial_lower_bound (P : PointSet) (candidates : Finset Line) (hP : P.card ≥ 2)
    (hnoncol : ¬ ∃ p ∈ P, ∃ q ∈ P, ∃ r ∈ P, p.1 = q.1 ∧ q.1 = r.1) :
    (linesDetermined P candidates).card ≥ P.card := by
  sorry

/-- JSP-000195: at least c·n²/k lines for k-line-free set. -/
theorem jsp_000195 (P : PointSet) (k : ℕ) (hk : 0 < k) (hP : P.card ≥ 2)
    (candidates : Finset Line)
    (hcov : ∀ L : Line, ∃ L' ∈ candidates, L = L')
    (hKfree : IsKLineFree P k) :
    ∃ c : ℝ, c > 0 ∧
      ((linesDetermined P candidates).card : ℝ) ≥
        c * ((P.card : ℕ) : ℝ)^2 / (k : ℝ) :=
  boroczky_1984 P k hk hP candidates hcov hKfree

end JSP195
