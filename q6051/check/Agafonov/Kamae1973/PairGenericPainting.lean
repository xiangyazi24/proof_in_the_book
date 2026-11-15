import Agafonov.Kamae1973.FiniteStagePainting
import Agafonov.Kamae1973.PaintingSchedule
import Agafonov.Kamae1973.FastProfileSubsequence
import Agafonov.Kamae1973.StageLawTransfer
import Agafonov.Kamae1973.StageAssembly
import Agafonov.Kamae1973.PaintedPairConvergence
import Agafonov.Kamae1973.PaintedWeightedNormality

/-!
# Pair-generic weighted-normal painting

A prescribed joining of a Bernoulli letter process with a binary limit profile
is realized along a rapidly growing sequence of profile endpoints.  Finite
stages are painted and assembled into one weighted-normal first coordinate;
the pair empirical laws converge to the prescribed joining at the shifted
endpoints.  This is the assembly of finite painting lemmas 17--20 in Kamae
(1973), Theorem 3, pp. 139--140.
-/

namespace Agafonov.Kamae1973

open Filter Topology
open scoped BigOperators

noncomputable section

/-- Every joining with Bernoulli first marginal and a binary profile as second
marginal is realized by a weighted-normal first coordinate along endpoints in
the original profile set.  This is the pair-generic painting conclusion in
Kamae (1973), Theorem 3, finite painting lemmas 17--20. -/
theorem exists_weightedNormal_pair_generic {b : ℕ}
    (P : LetterDistribution b) (t : ℕ → Bool)
    (S : Set ℕ) (μ : BlockFamily Bool)
    (ν : BlockFamily (Fin b × Bool))
    (hprofile : IsLimitProfile t S μ)
    (hfst : ∀ n : ℕ,
      ν.fst n = fun w : Fin n → Fin b => ∏ i, P.prob (w i))
    (hsnd : ∀ n : ℕ, ν.snd n = μ.law n) :
    ∃ x : ℕ → Fin b,
      IsWeightedNormal P x ∧
      ∃ N : ℕ → ℕ,
        StrictMono N ∧
        (∀ k, N k ∈ S) ∧
        ∀ n w,
          Tendsto
            (fun k =>
              empiricalLaw (fun i => (x i, t i)) (N k) n w)
            atTop (𝓝 (ν.law n w)) := by
  classical
  obtain ⟨N, hN, hmem, _hpositive, hnew, hratioBound,
      hmacroblocks, hmacro, hlookBound⟩ :=
    exists_fastProfileEndpoints P hprofile
  have hstageLength (k : ℕ) : 0 < N (k + 1) - N k :=
    Nat.sub_pos_of_lt (hN (Nat.lt_succ_self k))
  have hselectorStage (k : ℕ) :
      finiteLOne
          (intervalEmpiricalLaw t (N k) (N (k + 1) - N k)
            (stageParameters P k).blockLength)
          (μ.law (stageParameters P k).blockLength) ≤
        paintingTolerance k := by
    exact stageLaw_of_prefixLaws
      (x := t)
      (a := N k)
      (N := N (k + 1))
      (L := (stageParameters P k).blockLength)
      (q := μ.law (stageParameters P k).blockLength)
      (hN (Nat.lt_succ_self k))
      (paintingTolerance_pos k)
      (paintingTolerance_le_sixteenth k)
      (hnew k)
      (hratioBound k)
  have hpainting (k : ℕ) :
      ∃ u : Fin (N (k + 1) - N k) → Fin b,
        (∀ x : ℕ → Fin b, ExtendsInterval (N k) u x →
          ∀ r : ℕ, 1 ≤ r → r ≤ k + 1 →
            finiteLOne
              (intervalEmpiricalLaw (fun i => (x i, t i))
                (N k) (N (k + 1) - N k) r)
              (ν.law r) ≤ 15 * paintingTolerance k) ∧
        (∀ x : ℕ → Fin b, ExtendsInterval (N k) u x →
          ∀ s : ℕ, s ≤ N (k + 1) - N k →
            ∀ r : ℕ, 1 ≤ r → r ≤ k + 1 →
              ∀ w : Fin r → Fin b,
                |(intervalWordCount x (N k) s (List.ofFn w) : ℝ) -
                    (s : ℝ) * P.wordMass (List.ofFn w)| ≤
                  4 * paintingTolerance k * (s : ℝ) +
                    (stageParameters P k).macroLength) := by
    exact exists_finiteStagePainting
      P t μ ν
      (N k) (N (k + 1) - N k) (k + 1)
      (paintingTolerance_pos k)
      (stageParameters P k)
      (hstageLength k)
      (hmacroblocks k)
      (hmacro k)
      (hselectorStage k)
      hfst hsnd
  choose stage hpairRaw hprefixRaw using hpainting
  letI : Nonempty (Fin b) := ⟨P.positiveLetter⟩
  obtain ⟨x, _hinitial, hextends⟩ :=
    exists_sequence_extending_stages N hN P.positiveLetter stage
  have htolSixteenth :
      Tendsto (fun k => paintingTolerance k / 16) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (Filter.Tendsto.mul_const ((16 : ℝ)⁻¹)
        tendsto_paintingTolerance)
  have hratio :
      Tendsto
        (fun k => (N k : ℝ) / (N (k + 1) : ℝ))
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact Eventually.of_forall hratioBound
    · exact htolSixteenth
  have hlook :
      Tendsto
        (fun k =>
          ((stageParameters P k).macroLength : ℝ) / (N k : ℝ))
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact Eventually.of_forall hlookBound
    · exact tendsto_paintingTolerance
  have hpairStage :
      ∀ k r, 1 ≤ r → r ≤ k + 1 →
        finiteLOne
          (intervalEmpiricalLaw (fun i => (x i, t i))
            (N k) (N (k + 1) - N k) r)
          (ν.law r) ≤ 15 * paintingTolerance k := by
    intro k r hr hrk
    exact hpairRaw k x (hextends k) r hr hrk
  have hprefixStage :
      ∀ k s, s ≤ N (k + 1) - N k →
        ∀ r, 1 ≤ r → r ≤ k + 1 →
          ∀ w : Fin r → Fin b,
            |(intervalWordCount x (N k) s (List.ofFn w) : ℝ) -
                (s : ℝ) * P.wordMass (List.ofFn w)| ≤
              4 * paintingTolerance k * (s : ℝ) +
                (stageParameters P k).macroLength := by
    intro k s hs r hr hrk w
    exact hprefixRaw k x (hextends k) s hs r hr hrk w
  have hxnormal : IsWeightedNormal P x :=
    paintedStages_firstMarginal_allPrefixes
      P x N (fun k => (stageParameters P k).macroLength)
      hN paintingTolerance tendsto_paintingTolerance
      hratio hlook hprefixStage
  have hpairConverges :
      ∀ n w,
        Tendsto
          (fun k =>
            empiricalLaw (fun i => (x i, t i)) (N (k + 1)) n w)
          atTop (𝓝 (ν.law n w)) :=
    paintedStages_pairCoordinateConverge
      (fun i => (x i, t i)) ν N hN
      paintingTolerance tendsto_paintingTolerance hratio hpairStage
  refine ⟨x, hxnormal, fun k => N (k + 1), ?_, ?_, ?_⟩
  · intro i j hij
    exact hN (Nat.add_lt_add_right hij 1)
  · intro k
    exact hmem k
  · intro n w
    exact hpairConverges n w

end

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.exists_weightedNormal_pair_generic
