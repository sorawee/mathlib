/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser, Zhangir Azerbayev
-/

import linear_algebra.multilinear
import group_theory.perm.sign
import data.equiv.fin
import linear_algebra.tensor_product
import ring_theory.algebra_tower

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `semimodule` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.
-/

-- semiring / add_comm_monoid
variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [semimodule R M]
variables {N : Type*} [add_comm_monoid N] [semimodule R N]

-- semiring / add_comm_group
variables {L : Type*} [add_comm_group L] [semimodule R L]

-- ring / add_comm_group
variables {R' : Type*} [ring R']
variables {M' : Type*} [add_comm_group M'] [semimodule R' M']
variables {N' : Type*} [add_comm_group N'] [semimodule R' N']

variables {ι : Type*} [decidable_eq ι]

set_option old_structure_cmd true

section
variables (R M N ι)
/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure alternating_map extends multilinear_map R (λ i : ι, M) N :=
(map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0)
end

/-- The multilinear map associated to an alternating map -/
add_decl_doc alternating_map.to_multilinear_map

namespace alternating_map

variables (f f' : alternating_map R M N ι)
variables (g' : alternating_map R' M' N' ι)
variables (v : ι → M) (v' : ι → M')
open function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/
section coercions

instance : has_coe_to_fun (alternating_map R M N ι) := ⟨_, λ x, x.to_fun⟩

initialize_simps_projections alternating_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ :
  alternating_map R M N ι) = f := rfl

theorem congr_fun {f g : alternating_map R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
congr_arg (λ h : alternating_map R M N ι, h x) h

theorem congr_arg (f : alternating_map R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
congr_arg (λ x : ι → M, f x) h

theorem coe_inj ⦃f g : alternating_map R M N ι⦄ (h : ⇑f = g) : f = g :=
by { cases f, cases g, cases h, refl }

@[ext] theorem ext {f f' : alternating_map R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
coe_inj (funext H)

theorem ext_iff {f g : alternating_map R M N ι} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : has_coe (alternating_map R M N ι) (multilinear_map R (λ i : ι, M) N) :=
⟨λ x, x.to_multilinear_map⟩

@[simp, norm_cast] lemma coe_multilinear_map : ⇑(f : multilinear_map R (λ i : ι, M) N) = f := rfl

@[simp] lemma to_multilinear_map_eq_coe : f.to_multilinear_map = f := rfl

@[simp] lemma coe_multilinear_map_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : alternating_map R M N ι) :  multilinear_map R (λ i : ι, M) N) = ⟨f, h₁, h₂⟩ :=
rfl

end coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
-/
@[simp] lemma map_add (i : ι) (x y : M) :
  f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
f.to_multilinear_map.map_add' v i x y

@[simp] lemma map_sub (i : ι) (x y : M') :
  g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
g'.to_multilinear_map.map_sub v' i x y

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update v i (r • x)) = r • f (update v i x) :=
f.to_multilinear_map.map_smul' v i r x

@[simp] lemma map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_zero_of_eq' v i j h hij

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `semimodule` structure
as `multilinear_map`
-/

instance : has_add (alternating_map R M N ι) :=
⟨λ a b,
  { map_eq_zero_of_eq' :=
      λ v i j h hij, by simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij],
    ..(a + b : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma add_apply : (f + f') v = f v + f' v := rfl

instance : has_zero (alternating_map R M N ι) :=
⟨{map_eq_zero_of_eq' := λ v i j h hij, by simp,
  ..(0 : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma zero_apply : (0 : alternating_map R M N ι) v = 0 := rfl

instance : inhabited (alternating_map R M N ι) := ⟨0⟩

instance : add_comm_monoid (alternating_map R M N ι) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

instance : has_neg (alternating_map R' M' N' ι) :=
⟨λ f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..(-(f : multilinear_map R' (λ i : ι, M') N')) }⟩

@[simp] lemma neg_apply (m : ι → M') : (-g') m = - (g' m) := rfl

instance : add_comm_group (alternating_map R' M' N' ι) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..alternating_map.add_comm_monoid, ..};
   intros; ext; simp [add_comm, add_left_comm]

section semimodule

variables {S : Type*} [comm_semiring S] [algebra S R] [semimodule S N]
  [is_scalar_tower S R N]

instance : has_scalar S (alternating_map R M N ι) :=
⟨λ c f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..((c • f : multilinear_map R (λ i : ι, M) N)) }⟩

@[simp] lemma smul_apply (f : alternating_map R M N ι) (c : S) (m : ι → M) :
  (c • f) m = c • f m := rfl

/-- The space of multilinear maps over an algebra over `S` is a module over `S`, for the pointwise
addition and scalar multiplication. -/
instance : semimodule S (alternating_map R M N ι) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

end semimodule

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
-/

lemma map_update_self {i j : ι} (hij : i ≠ j) :
  f (function.update v i (v j)) = 0 :=
f.map_eq_zero_of_eq _ (by rw [function.update_same, function.update_noteq hij.symm]) hij

lemma map_update_update {i j : ι} (hij : i ≠ j) (m : M) :
  f (function.update (function.update v i m) j m) = 0 :=
f.map_eq_zero_of_eq _
  (by rw [function.update_same, function.update_noteq hij, function.update_same]) hij

lemma map_swap_add {i j : ι} (hij : i ≠ j) :
  f (v ∘ equiv.swap i j) + f v = 0 :=
begin
  rw equiv.comp_swap_eq_update,
  convert f.map_update_update v hij (v i + v j),
  simp [f.map_update_self _ hij,
        f.map_update_self _ hij.symm,
        function.update_comm hij (v i + v j) (v _) v,
        function.update_comm hij.symm (v i) (v i) v],
end

lemma map_add_swap {i j : ι} (hij : i ≠ j) :
  f v + f (v ∘ equiv.swap i j) = 0 :=
by { rw add_comm, exact f.map_swap_add v hij }

variable (g : alternating_map R M L ι)

lemma map_swap {i j : ι} (hij : i ≠ j) :
  g (v ∘ equiv.swap i j) = - g v  :=
eq_neg_of_add_eq_zero (g.map_swap_add v hij)

lemma map_perm [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
  g (v ∘ σ) = (equiv.perm.sign σ : ℤ) • g v :=
begin
  apply equiv.perm.swap_induction_on' σ,
  { simp },
  { intros s x y hxy hI,
    simpa [g.map_swap (v ∘ s) hxy, equiv.perm.sign_swap hxy] using hI, }
end

lemma map_perm' [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
  g (λ i, v (σ i)) = (equiv.perm.sign σ : ℤ) • g v :=
g.map_perm v σ

lemma map_congr_perm [fintype ι] (σ : equiv.perm ι) :
  g v = (equiv.perm.sign σ : ℤ) • g (v ∘ σ) :=
by { rw [g.map_perm, smul_smul], simp }

end alternating_map

section

namespace alternating_map

open_locale big_operators
open_locale tensor_product

/-- A setoid between equivalences which do not swap `sum.inl` with `sum.inr`. -/
def mod_sum_congr (α β : Type*) : setoid (equiv.perm (α ⊕ β)) :=
{ r := λ σ₁ σ₂, ∃ (sl : equiv.perm α) (sr : equiv.perm β), σ₁ = σ₂ * (equiv.sum_congr sl sr : equiv.perm (α ⊕ β)),
  iseqv := ⟨
    λ σ, ⟨1, 1, by simp [equiv.perm.mul_def, equiv.perm.one_def]⟩,
    λ σ₁ σ₂ ⟨sl, sr, h⟩, ⟨sl⁻¹, sr⁻¹, by {
      rw [h, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩,
    λ σ₁ σ₂ σ₃ ⟨sl₁₂, sr₁₂, h₁₂⟩ ⟨sl₂₃, sr₂₃, h₂₃⟩, ⟨sl₂₃ * sl₁₂, sr₂₃ * sr₁₂, by {
      rw [h₁₂, h₂₃, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩
⟩}

def sum_congr_subgroup (α β : Type*) : subgroup (equiv.perm (α ⊕ β)) :=
{ carrier := λ σ, ∃ (sl : equiv.perm α) (sr : equiv.perm β), σ = equiv.perm.sum_congr sl sr,
  one_mem' := ⟨1, 1, equiv.perm.sum_congr_one.symm⟩,
  mul_mem' := λ σ₁ σ₂ ⟨sl₁₂, sr₁₂, h₁₂⟩ ⟨sl₂₃, sr₂₃, h₂₃⟩,
    ⟨sl₁₂ * sl₂₃, sr₁₂ * sr₂₃, h₂₃.symm ▸ h₁₂.symm ▸ equiv.perm.sum_congr_mul _ _ _ _⟩,
  inv_mem' := λ σ₁ ⟨sl, sr, h⟩, ⟨sl⁻¹, sr⁻¹, h.symm ▸ equiv.perm.sum_congr_inv _ _⟩

#check quotient_group.quotient

def mod_sum_congr' (α β : Type*) := quotient_group.quotient $ sum_congr_subgroup α β

instance {α β : Type*} [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_rel (mod_sum_congr α β).r :=
λ σ₁ σ₂, fintype.decidable_exists_fintype

section coprod

variables {ιa ιb : Type*} [decidable_eq ιa] [decidable_eq ιb] [fintype ιa] [fintype ιb]

private def dom_coprod_aux
  {R : Type*} {M N : Type*}
  [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N ιa) (b : alternating_map R M N ιb)
  (v : ιa ⊕ ιb → M) : N :=
let ab := (algebra.lmul' R).comp_multilinear_map
  $ multilinear_map.dom_coprod a.to_multilinear_map b.to_multilinear_map in
∑ σ : quotient (mod_sum_congr ιa ιb), σ.lift_on' (λ σ, (σ.sign : ℤ) • (ab.dom_dom_congr σ) v)
(λ σ₁ σ₂ h, begin
  dsimp only [ab],
  simp only [linear_map.comp_multilinear_map_dom_dom_congr,
              linear_map.comp_multilinear_map_apply,
              multilinear_map.dom_dom_congr_apply,
              multilinear_map.dom_coprod_apply,
              algebra.lmul'_apply,
              to_multilinear_map_eq_coe,
              coe_multilinear_map],
  obtain ⟨sl, sr, rfl⟩ := h,
  have : ((sl.sign : ℤ) • a (λ i, v $ σ₂ $ sum.inl $ sl i)) *
          ((sr.sign : ℤ) • b (λ i, v $ σ₂ $ sum.inr $ sr i)) = a (λ i, v $ σ₂ $ sum.inl i)
                                                            * b (λ i, v $ σ₂ $ sum.inr i) := by {
    rw [a.map_perm' (λ i, v (σ₂ (sum.inl i))), b.map_perm' (λ i, v (σ₂ (sum.inr i)))],
    simp only [smul_smul, int.units_coe_mul_self, one_smul],
  },
  rw ←this,
  have : ((σ₂ * equiv.sum_congr sl sr).sign : ℤ) = σ₂.sign * (sl.sign * sr.sign) := by simp,
  rw [this, mul_smul, mul_smul],
  simp only [sum.map_inr, equiv.perm.sum_congr_apply, sum.map_inl, algebra.mul_smul_comm,
             function.comp_app, equiv.perm.coe_mul, algebra.smul_mul_assoc],
end)


#check 1


instance asasd {α β : Type*} [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_rel $ (quotient_group.left_rel (sum_congr_subgroup α β)).r :=
λ σ₁ σ₂, fintype.decidable_exists_fintype

instance : fintype (mod_sum_congr' ιa ιb) := quotient.fintype _

private def dom_coprod_aux
  {R : Type*} {M N : Type*}
  [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N ιa) (b : alternating_map R M N ιb)
  (v : ιa ⊕ ιb → M) : N :=
let ab := (algebra.lmul' R).comp_multilinear_map
  $ multilinear_map.dom_coprod a.to_multilinear_map b.to_multilinear_map in
∑ σ : mod_sum_congr' ιa ιb, σ.lift_on' (λ σ, (σ.sign : ℤ) • (ab.dom_dom_congr σ) v)
(λ σ₁ σ₂ h, begin
  dsimp only [ab],
  simp only [linear_map.comp_multilinear_map_dom_dom_congr,
              linear_map.comp_multilinear_map_apply,
              multilinear_map.dom_dom_congr_apply,
              multilinear_map.dom_coprod_apply,
              algebra.lmul'_apply,
              to_multilinear_map_eq_coe,
              coe_multilinear_map],
  dunfold quotient_group.left_rel setoid.r at h,
  obtain ⟨sl, sr, h⟩ := h,
  rw inv_mul_eq_iff_eq_mul at h,
  rw h,
  have : ((sl.sign : ℤ) • a (λ i, v $ σ₁ $ sum.inl $ sl i)) *
          ((sr.sign : ℤ) • b (λ i, v $ σ₁ $ sum.inr $ sr i)) = a (λ i, v $ σ₁ $ sum.inl i)
                                                            * b (λ i, v $ σ₁ $ sum.inr i) := by {
    rw [a.map_perm' (λ i, v (σ₁ (sum.inl i))), b.map_perm' (λ i, v (σ₁ (sum.inr i)))],
    simp only [smul_smul, int.units_coe_mul_self, one_smul],
  },
  rw ←this,
  have : ((σ₁ * equiv.sum_congr sl sr).sign : ℤ) = σ₁.sign * (sl.sign * sr.sign) := by simp,
  rw [this, mul_smul, mul_smul],
  simp only [sum.map_inr, equiv.perm.sum_congr_apply, sum.map_inl, algebra.mul_smul_comm,
             function.comp_app, equiv.perm.coe_mul, algebra.smul_mul_assoc],
end)

private lemma dom_coprod_aux_eq_zero_if_eq
  {R : Type*} {M N : Type*}
  [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N ιa) (b : alternating_map R M N ιb)
  (v : ιa ⊕ ιb → M) (i j : ιa ⊕ ιb) (h : v i = v j) (hij : i ≠ j) :
  dom_coprod_aux a b v = 0 :=
begin
  unfold dom_coprod_aux,
  dsimp only,
  apply finset.sum_cancels_of_partition_cancels _,
  intros σ _,
  /-
  ⊢ ∑ (σ : quotient (mod_sum_congr ιa ιb)),
        σ.lift_on'
          (λ (σ : equiv.perm (ιa ⊕ ιb)),
            ↑(⇑equiv.perm.sign σ) •
              ⇑(multilinear_map.dom_dom_congr σ
                    ((algebra.lmul' R).comp_multilinear_map (a.to_multilinear_map.dom_coprod b.to_multilinear_map)))
                v)
          _ =
      0
  -/
  -- TODO: express this as part of a larger sum over the full space of `equiv.perm (ιa ⊕ ιb)`
  sorry,
end

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note this is the same as `(multilinear_map.dom_coprod a b).alternize / (card ιa)! / (card ιb)!`.-/
def dom_coprod
  {R : Type*} {M N : Type*}
  [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N ιa) (b : alternating_map R M N ιb) :
  alternating_map R M N (ιa ⊕ ιb) :=
{ to_fun := dom_coprod_aux a b,
  map_add' := λ v i p q, begin
    dsimp only [dom_coprod_aux],
    simp_rw [←finset.sum_add_distrib, multilinear_map.map_add, smul_add],
    congr' 1,
    ext σ',
    obtain ⟨σ, rfl⟩ := quot.exists_rep σ',
    refl,
  end,
  map_smul' := λ v i c p, begin
    dsimp only [dom_coprod_aux],
    simp_rw [finset.smul_sum, multilinear_map.map_smul, smul_comm],
    congr' 1,
    ext σ',
    obtain ⟨σ, rfl⟩ := quot.exists_rep σ',
    refl,
  end,
  map_eq_zero_of_eq' := dom_coprod_aux_eq_zero_if_eq a b }

-- ### Old version, before generalizing to arbitrary index types
--
-- def mul_fin {n m} {R : Type*} {M N : Type*}
--   [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
--   (a : alternating_map R M N (fin m)) (b : alternating_map R M N (fin n)) :
--   alternating_map R M N (fin (m + n)) :=
-- { to_fun :=
--     let ab := (algebra.lmul' R).comp_multilinear_map
--       $ multilinear_map.dom_coprod a.to_multilinear_map b.to_multilinear_map in
--     λ (v : fin (m + n) → M),
--     ∑ σ : shuffle m n, (σ.to_perm.sign : ℤ) • (ab.dom_dom_congr σ.val) v,
--   map_add' := λ v i p q, by simp_rw [←finset.sum_add_distrib, ←smul_add, multilinear_map.map_add],
--   map_smul' := λ v i c p, by simp_rw [finset.smul_sum, ←smul_comm, multilinear_map.map_smul],
--   map_eq_zero_of_eq' := λ v i j h hij, begin
--     sorry
--   end }

end coprod

end alternating_map

end