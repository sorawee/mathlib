/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

-/
import data.dfinsupp

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open_locale big_operators

universes u v w u₁

variables (ι : Type v) [dec_ι : decidable_eq ι] (β : ι → Type w) [Π i, add_comm_monoid (β i)]

/-- `direct_sum β` is the direct sum of a family of additive commutative groups `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
def direct_sum : Type* := Π₀ i, β i

localized "notation `⨁` binders `, ` r:(scoped f, direct_sum _ f) := r" in direct_sum

namespace direct_sum2

variables {ι β}

instance : add_comm_monoid (⨁ i, β i) :=
dfinsupp.add_comm_monoid

instance : inhabited (⨁ i, β i) := ⟨0⟩

variables β

include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk : Π s : finset ι, (Π i : (↑s : set ι), β i.1) → ⨁ i, β i :=
dfinsupp.mk

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of : Π i : ι, β i → ⨁ i, β i :=
dfinsupp.single
variables {β}

instance mk.is_add_group_hom (s : finset ι) : is_add_monoid_hom (mk β s) :=
{ map_add := λ _ _, dfinsupp.mk_add,
  map_zero := dfinsupp.mk_zero }

@[simp] lemma mk_zero (s : finset ι) : mk β s 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma mk_add (s : finset ι) (x y) : mk β s (x + y) = mk β s x + mk β s y :=
is_add_hom.map_add _ x y

instance of.is_add_group_hom (i : ι) : is_add_monoid_hom (of β i) :=
{ map_add := λ _ _, dfinsupp.single_add,
  map_zero := dfinsupp.single_zero }

@[simp] lemma of_zero (i : ι) : of β i 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma of_add (i : ι) (x y) : of β i (x + y) = of β i x + of β i y :=
is_add_hom.map_add _ x y

theorem mk_injective (s : finset ι) : function.injective (mk β s) :=
dfinsupp.mk_injective s

theorem of_injective (i : ι) : function.injective (of β i) :=
λ x y H, congr_fun (mk_injective _ H) ⟨i, by simp⟩

@[elab_as_eliminator]
protected theorem induction_on {C : (⨁ i, β i) → Prop}
  (x : ⨁ i, β i) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

variables {γ : Type u₁} [add_comm_monoid γ]
variables (φ : Π i, β i → γ) [Π i, is_add_monoid_hom (φ i)]

variables (φ)
/-- `to_group φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def to_monoid(f : ⨁ i, β i) : γ :=
quotient.lift_on f (λ x, ∑ i in x.2.to_finset, φ i (x.1 i)) $ λ x y H,
begin
  have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
  have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
  refine (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
  { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(y.3 i).resolve_left (mt (and.intro H1) H2), is_add_monoid_hom.map_zero (φ i)] },
  { intros i H1, rw H i },
  { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), is_add_monoid_hom.map_zero (φ i)] }
end
variables {φ}

instance to_monoid.is_add_monoid_hom : is_add_monoid_hom (to_monoid φ) :=
{ map_add := assume f g,
begin
  refine quotient.induction_on f (λ x, _),
  refine quotient.induction_on g (λ y, _),
  change ∑ i in _, _ = (∑ i in _, _) + (∑ i in _, _),
  simp only, conv { to_lhs, congr, skip, funext, rw is_add_hom.map_add (φ i) },
  simp only [finset.sum_add_distrib],
  congr' 1,
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(x.3 i).resolve_left H2, is_add_monoid_hom.map_zero (φ i)] } },
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(y.3 i).resolve_left H2, is_add_monoid_hom.map_zero (φ i)] } }
end,
  map_zero := rfl }

variables (φ)
@[simp] lemma to_monoid_zero : to_monoid φ 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma to_monoid_add (x y) : to_monoid φ (x + y) = to_monoid φ x + to_monoid φ y :=
is_add_hom.map_add _ x y

@[simp] lemma to_monoid_of (i) (x : β i) : to_monoid φ (of β i x) = φ i x :=
(add_zero _).trans $ congr_arg (φ i) $ show (if H : i ∈ ({i} : finset _) then x else 0) = x,
from dif_pos $ finset.mem_singleton_self i

variables (ψ : (⨁ i, β i) → γ) [is_add_monoid_hom ψ]

theorem to_monoid.unique (f : ⨁ i, β i) :
  ψ f = @to_monoid _ _ _ _ _ _ (λ i, ψ ∘ of β i) (λ i, is_add_monoid_hom.comp (of β i) ψ) f :=
by haveI : ∀ i, is_add_monoid_hom (ψ ∘ of β i) := (λ _, is_add_monoid_hom.comp _ _); exact
direct_sum2.induction_on f
  (by rw [is_add_monoid_hom.map_zero ψ, is_add_monoid_hom.map_zero (to_monoid (λ i, ψ ∘ of β i))])
  (λ i x, by rw [to_monoid_of])
  (λ x y ihx ihy, by rw [is_add_hom.map_add ψ, is_add_hom.map_add (to_monoid (λ i, ψ ∘ of β i)), ihx, ihy])

variables (β)
/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
-- TODO: generalize this to remove the assumption `S ⊆ T`.
def set_to_set (S T : set ι) (H : S ⊆ T) :
  (⨁ (i : S), β i) → (⨁ (i : T), β i) :=
to_monoid $ λ i, of (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩
variables {β}

instance (S T : set ι) (H : S ⊆ T) : is_add_monoid_hom (set_to_set β S T H) :=
to_monoid.is_add_monoid_hom

omit dec_ι

/-- The natural equivalence between `⨁ _ : punit, M` and `M`. -/
-- TODO: generalize this to a sum over any type `ι` that is `unique ι`.
protected def id (M : Type v) [add_comm_monoid M] : (⨁ (_ : punit), M) ≃ M :=
{ to_fun := direct_sum2.to_monoid (λ _, id),
  inv_fun := of (λ _, M) punit.star,
  left_inv := λ x, direct_sum2.induction_on x
    (by rw [to_monoid_zero, of_zero])
    (λ ⟨⟩ x, by rw [to_monoid_of]; refl)
    (λ x y ihx ihy, by rw [to_monoid_add, of_add, ihx, ihy]),
  right_inv := λ x, to_monoid_of _ _ _ }

instance : has_coe_to_fun (⨁ i, β i) :=
dfinsupp.has_coe_to_fun

end direct_sum2