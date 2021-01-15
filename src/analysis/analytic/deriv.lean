import analysis.analytic.basic
import analysis.calculus.fderiv

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]

open_locale topological_space classical big_operators nnreal
open set filter asymptotics

variables {f g : E → F} {p pf pg : formal_multilinear_series 𝕜 E F} {x : E} {r r' : ennreal}

lemma has_fpower_series_at.has_fderiv_at (hf : has_fpower_series_at f p x) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  rw has_fderiv_at_iff_is_o_nhds_zero,
  refine ((has_fpower_series_at.is_O_sub_partial_sum_pow hf 2).trans_is_o
    (is_o_norm_pow_id one_lt_two)).congr_left (λ y, _),
  have : (fin.snoc 0 y : fin 1 → E) = λ _, y,
  { ext i, rw [show i = fin.last 0, from subsingleton.elim _ _, fin.snoc_last] },
  simp [formal_multilinear_series.partial_sum, finset.range_succ, sub_add_eq_sub_sub_swap,
    hf.coeff_zero, this]
end

lemma has_fpower_series_at.has_strict_fderiv_at (hf : has_fpower_series_at f p x) :
  has_strict_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  rw [has_strict_fderiv_at, ← map_add_left_nhds_zero, is_o_map],
  have : ∀ y, (fin.snoc 0 y : fin 1 → E) = λ _, y,
  { intro y, ext i, rw [show i = fin.last 0, from subsingleton.elim _ _, fin.snoc_last] },
  simp [(∘), this], -- TODO squeeze
  
end
