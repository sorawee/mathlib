/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.limits.types
import category_theory.limits.preserves
import algebra.pi_instances

/-!
# The category of abelian groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

## Further work
A lot of this should be generalised / automated, as it's quite common for concrete
categories that the forgetful functor preserves limits.
-/

open category_theory
open category_theory.limits

universe u

namespace AddCommGroup

variables {J : Type u} [small_category J]

instance add_comm_group_obj (F : J ⥤ AddCommGroup) (j) :
  add_comm_group ((F ⋙ forget AddCommGroup).obj j) :=
by { change add_comm_group (F.obj j), apply_instance }

instance sections_add_submonoid (F : J ⥤ AddCommGroup) :
  is_add_submonoid (F ⋙ forget AddCommGroup).sections :=
{ zero_mem := λ j j' f, by simp,
  add_mem := λ a b ah bh j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, add_monoid_hom.map_add, pi.add_apply],
    dsimp [functor.sections] at ah bh,
    rw [ah f, bh f],
  end }

instance sections_add_subgroup (F : J ⥤ AddCommGroup) :
  is_add_subgroup (F ⋙ forget AddCommGroup).sections :=
{ neg_mem := λ a ah j j' f,
  begin
    simp only [forget_map_eq_coe, functor.comp_map, pi.neg_apply, add_monoid_hom.map_neg, neg_inj],
    dsimp [functor.sections] at ah,
    rw ah f,
  end,
  ..(AddCommGroup.sections_add_submonoid F) }

instance limit_add_comm_group (F : J ⥤ AddCommGroup) :
  add_comm_group (limit (F ⋙ forget AddCommGroup)) :=
@subtype.add_comm_group ((Π (j : J), (F ⋙ forget _).obj j)) (by apply_instance) _
  (by convert (AddCommGroup.sections_add_subgroup F))

/-- `limit.π (F ⋙ forget AddCommGroup) j` as a `add_monoid_hom`. -/
def limit_π_add_monoid_hom (F : J ⥤ AddCommGroup) (j) :
  limit (F ⋙ forget AddCommGroup) →+ (F ⋙ forget AddCommGroup).obj j :=
{ to_fun := limit.π (F ⋙ forget AddCommGroup) j,
  map_zero' := by { simp only [types.types_limit_π], refl },
  map_add' := λ x y, by { simp only [types.types_limit_π], refl } }

namespace AddCommGroup_has_limits
-- The next two definitions are used in the construction of `has_limits AddCommGroup`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `AddCommGroup`.
(Internal use only; use the limits API.)
-/
def limit (F : J ⥤ AddCommGroup) : cone F :=
{ X := AddCommGroup.of (limit (F ⋙ forget _)),
  π :=
  { app := limit_π_add_monoid_hom F,
    naturality' := λ j j' f,
      add_monoid_hom.coe_inj ((limit.cone (F ⋙ forget _)).π.naturality f) } }

/--
Witness that the limit cone in `AddCommGroup` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_is_limit (F : J ⥤ AddCommGroup) : is_limit (limit F) :=
begin
  refine is_limit.of_faithful
    (forget AddCommGroup) (limit.is_limit _)
    (λ s, ⟨_, _, _⟩) (λ s, rfl); tidy,
end

end AddCommGroup_has_limits
open AddCommGroup_has_limits

/-- The category of abelian groups has all limits. -/
instance AddCommGroup_has_limits : has_limits AddCommGroup :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI
    { cone     := limit F,
      is_limit := limit_is_limit F } } }

/--
The forgetful functor from abelian groups to types preserves all limits. (That is, the underlying
types could have been computed instead as limits in the category of types.)
-/
instance forget_preserves_limits : preserves_limits (forget AddCommGroup) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit.is_limit F) (limit.is_limit (F ⋙ forget _)) } }

end AddCommGroup
